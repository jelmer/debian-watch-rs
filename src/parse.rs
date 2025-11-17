use crate::lex::lex;
use crate::types::*;
use crate::SyntaxKind;
use crate::SyntaxKind::*;
use crate::DEFAULT_VERSION;
use std::marker::PhantomData;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParseError(Vec<String>);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for err in &self.0 {
            writeln!(f, "{}", err)?;
        }
        Ok(())
    }
}

impl std::error::Error for ParseError {}

/// Second, implementing the `Language` trait teaches rowan to convert between
/// these two SyntaxKind types, allowing for a nicer SyntaxNode API where
/// "kinds" are values from our `enum SyntaxKind`, instead of plain u16 values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Lang {}
impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }
    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        kind.into()
    }
}

/// GreenNode is an immutable tree, which is cheap to change,
/// but doesn't contain offsets and parent pointers.
use rowan::GreenNode;

/// You can construct GreenNodes by hand, but a builder
/// is helpful for top-down parsers: it maintains a stack
/// of currently in-progress nodes
use rowan::GreenNodeBuilder;

/// Thread-safe parse result that can be stored in incremental computation systems like Salsa.
/// The type parameter T represents the root AST node type (e.g., WatchFile).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parse<T> {
    /// The immutable green tree that can be shared across threads
    green: GreenNode,
    /// Parse errors encountered during parsing
    errors: Vec<String>,
    /// Phantom type to associate this parse result with a specific AST type
    _ty: PhantomData<T>,
}

impl<T> Parse<T> {
    /// Create a new parse result
    fn new(green: GreenNode, errors: Vec<String>) -> Self {
        Parse {
            green,
            errors,
            _ty: PhantomData,
        }
    }

    /// Get the green node
    pub fn green(&self) -> &GreenNode {
        &self.green
    }

    /// Get the parse errors
    pub fn errors(&self) -> &[String] {
        &self.errors
    }

    /// Check if there were any parse errors
    pub fn is_ok(&self) -> bool {
        self.errors.is_empty()
    }
}

impl Parse<WatchFile> {
    /// Get the root WatchFile node
    pub fn tree(&self) -> WatchFile {
        WatchFile::cast(SyntaxNode::new_root(self.green.clone()))
            .expect("root node should be a WatchFile")
    }
}

// The internal parse result used during parsing
struct InternalParse {
    green_node: GreenNode,
    errors: Vec<String>,
}

fn parse(text: &str) -> InternalParse {
    struct Parser {
        /// input tokens, including whitespace,
        /// in *reverse* order.
        tokens: Vec<(SyntaxKind, String)>,
        /// the in-progress tree.
        builder: GreenNodeBuilder<'static>,
        /// the list of syntax errors we've accumulated
        /// so far.
        errors: Vec<String>,
    }

    impl Parser {
        fn parse_version(&mut self) -> Option<u32> {
            let mut version = None;
            if self.tokens.last() == Some(&(KEY, "version".to_string())) {
                self.builder.start_node(VERSION.into());
                self.bump();
                self.skip_ws();
                if self.current() != Some(EQUALS) {
                    self.builder.start_node(ERROR.into());
                    self.errors.push("expected `=`".to_string());
                    self.bump();
                    self.builder.finish_node();
                } else {
                    self.bump();
                }
                if self.current() != Some(VALUE) {
                    self.builder.start_node(ERROR.into());
                    self.errors
                        .push(format!("expected value, got {:?}", self.current()));
                    self.bump();
                    self.builder.finish_node();
                } else if let Some((_, value)) = self.tokens.last() {
                    let version_str = value;
                    match version_str.parse() {
                        Ok(v) => {
                            version = Some(v);
                            self.bump();
                        }
                        Err(_) => {
                            self.builder.start_node(ERROR.into());
                            self.errors
                                .push(format!("invalid version: {}", version_str));
                            self.bump();
                            self.builder.finish_node();
                        }
                    }
                } else {
                    self.builder.start_node(ERROR.into());
                    self.errors.push("expected version value".to_string());
                    self.builder.finish_node();
                }
                if self.current() != Some(NEWLINE) {
                    self.builder.start_node(ERROR.into());
                    self.errors.push("expected newline".to_string());
                    self.bump();
                    self.builder.finish_node();
                } else {
                    self.bump();
                }
                self.builder.finish_node();
            }
            version
        }

        fn parse_watch_entry(&mut self) -> bool {
            self.skip_ws();
            if self.current().is_none() {
                return false;
            }
            if self.current() == Some(NEWLINE) {
                self.bump();
                return false;
            }
            self.builder.start_node(ENTRY.into());
            self.parse_options_list();
            for i in 0..4 {
                if self.current() == Some(NEWLINE) {
                    break;
                }
                if self.current() == Some(CONTINUATION) {
                    self.bump();
                    self.skip_ws();
                    continue;
                }
                if self.current() != Some(VALUE) && self.current() != Some(KEY) {
                    self.builder.start_node(ERROR.into());
                    self.errors.push(format!(
                        "expected value, got {:?} (i={})",
                        self.current(),
                        i
                    ));
                    if self.current().is_some() {
                        self.bump();
                    }
                    self.builder.finish_node();
                } else {
                    self.bump();
                }
                self.skip_ws();
            }
            if self.current() != Some(NEWLINE) && self.current().is_some() {
                self.builder.start_node(ERROR.into());
                self.errors
                    .push(format!("expected newline, not {:?}", self.current()));
                if self.current().is_some() {
                    self.bump();
                }
                self.builder.finish_node();
            } else {
                self.bump();
            }
            self.builder.finish_node();
            true
        }

        fn parse_option(&mut self) -> bool {
            if self.current().is_none() {
                return false;
            }
            while self.current() == Some(CONTINUATION) {
                self.bump();
            }
            if self.current() == Some(WHITESPACE) {
                return false;
            }
            self.builder.start_node(OPTION.into());
            if self.current() != Some(KEY) {
                self.builder.start_node(ERROR.into());
                self.errors.push("expected key".to_string());
                self.bump();
                self.builder.finish_node();
            } else {
                self.bump();
            }
            if self.current() == Some(EQUALS) {
                self.bump();
                if self.current() != Some(VALUE) && self.current() != Some(KEY) {
                    self.builder.start_node(ERROR.into());
                    self.errors
                        .push(format!("expected value, got {:?}", self.current()));
                    self.bump();
                    self.builder.finish_node();
                } else {
                    self.bump();
                }
            } else if self.current() == Some(COMMA) {
            } else {
                self.builder.start_node(ERROR.into());
                self.errors.push("expected `=`".to_string());
                if self.current().is_some() {
                    self.bump();
                }
                self.builder.finish_node();
            }
            self.builder.finish_node();
            true
        }

        fn parse_options_list(&mut self) {
            self.skip_ws();
            if self.tokens.last() == Some(&(KEY, "opts".to_string()))
                || self.tokens.last() == Some(&(KEY, "options".to_string()))
            {
                self.builder.start_node(OPTS_LIST.into());
                self.bump();
                self.skip_ws();
                if self.current() != Some(EQUALS) {
                    self.builder.start_node(ERROR.into());
                    self.errors.push("expected `=`".to_string());
                    if self.current().is_some() {
                        self.bump();
                    }
                    self.builder.finish_node();
                } else {
                    self.bump();
                }
                let quoted = if self.current() == Some(QUOTE) {
                    self.bump();
                    true
                } else {
                    false
                };
                loop {
                    if quoted {
                        if self.current() == Some(QUOTE) {
                            self.bump();
                            break;
                        }
                        self.skip_ws();
                    }
                    if !self.parse_option() {
                        break;
                    }
                    if self.current() == Some(COMMA) {
                        self.bump();
                    } else if !quoted {
                        break;
                    }
                }
                self.builder.finish_node();
                self.skip_ws();
            }
        }

        fn parse(mut self) -> InternalParse {
            // Make sure that the root node covers all source
            self.builder.start_node(ROOT.into());
            if let Some(_v) = self.parse_version() {
                // Version is stored in the syntax tree, no need to track separately
            }
            // TODO: use version to influence parsing
            loop {
                if !self.parse_watch_entry() {
                    break;
                }
            }
            // Don't forget to eat *trailing* whitespace
            self.skip_ws();
            // Close the root node.
            self.builder.finish_node();

            // Turn the builder into a GreenNode
            InternalParse {
                green_node: self.builder.finish(),
                errors: self.errors,
            }
        }
        /// Advance one token, adding it to the current branch of the tree builder.
        fn bump(&mut self) {
            if let Some((kind, text)) = self.tokens.pop() {
                self.builder.token(kind.into(), text.as_str());
            }
        }
        /// Peek at the first unprocessed token
        fn current(&self) -> Option<SyntaxKind> {
            self.tokens.last().map(|(kind, _)| *kind)
        }
        fn skip_ws(&mut self) {
            while self.current() == Some(WHITESPACE)
                || self.current() == Some(CONTINUATION)
                || self.current() == Some(COMMENT)
            {
                self.bump()
            }
        }
    }

    let mut tokens = lex(text);
    tokens.reverse();
    Parser {
        tokens,
        builder: GreenNodeBuilder::new(),
        errors: Vec::new(),
    }
    .parse()
}

/// To work with the parse results we need a view into the
/// green tree - the Syntax tree.
/// It is also immutable, like a GreenNode,
/// but it contains parent pointers, offsets, and
/// has identity semantics.
type SyntaxNode = rowan::SyntaxNode<Lang>;
#[allow(unused)]
type SyntaxToken = rowan::SyntaxToken<Lang>;
#[allow(unused)]
type SyntaxElement = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;

impl InternalParse {
    fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green_node.clone())
    }

    fn root(&self) -> WatchFile {
        WatchFile::cast(self.syntax()).expect("root node should be a WatchFile")
    }
}

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        /// A node in the syntax tree for $ast
        pub struct $ast(SyntaxNode);
        impl $ast {
            #[allow(unused)]
            fn cast(node: SyntaxNode) -> Option<Self> {
                if node.kind() == $kind {
                    Some(Self(node))
                } else {
                    None
                }
            }
        }

        impl std::fmt::Display for $ast {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}", self.0.text())
            }
        }
    };
}

ast_node!(WatchFile, ROOT);
ast_node!(Version, VERSION);
ast_node!(Entry, ENTRY);
ast_node!(OptionList, OPTS_LIST);
ast_node!(_Option, OPTION);

impl WatchFile {
    /// Create a new watch file with specified version
    pub fn new(version: Option<u32>) -> WatchFile {
        let mut builder = GreenNodeBuilder::new();

        builder.start_node(ROOT.into());
        if let Some(version) = version {
            builder.start_node(VERSION.into());
            builder.token(KEY.into(), "version");
            builder.token(EQUALS.into(), "=");
            builder.token(VALUE.into(), version.to_string().as_str());
            builder.token(NEWLINE.into(), "\n");
            builder.finish_node();
        }
        builder.finish_node();
        WatchFile(SyntaxNode::new_root(builder.finish()))
    }

    /// Returns the version of the watch file.
    pub fn version(&self) -> u32 {
        self.0
            .children()
            .find_map(Version::cast)
            .map(|it| it.version())
            .unwrap_or(DEFAULT_VERSION)
    }

    /// Returns an iterator over all entries in the watch file.
    pub fn entries(&self) -> impl Iterator<Item = Entry> + '_ {
        self.0.children().filter_map(Entry::cast)
    }
}

impl FromStr for WatchFile {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parsed = parse(s);
        if parsed.errors.is_empty() {
            Ok(parsed.root())
        } else {
            Err(ParseError(parsed.errors))
        }
    }
}

/// Parse a watch file and return a thread-safe parse result.
/// This can be stored in incremental computation systems like Salsa.
pub fn parse_watch_file(text: &str) -> Parse<WatchFile> {
    let parsed = parse(text);
    Parse::new(parsed.green_node, parsed.errors)
}

impl Version {
    /// Returns the version of the watch file.
    pub fn version(&self) -> u32 {
        self.0
            .children_with_tokens()
            .find_map(|it| match it {
                SyntaxElement::Token(token) => {
                    if token.kind() == VALUE {
                        token.text().parse().ok()
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .unwrap_or(DEFAULT_VERSION)
    }
}

impl Entry {
    /// List of options
    pub fn option_list(&self) -> Option<OptionList> {
        self.0.children().find_map(OptionList::cast)
    }

    /// Get the value of an option
    pub fn get_option(&self, key: &str) -> Option<String> {
        self.option_list().and_then(|ol| ol.get_option(key))
    }

    /// Check if an option is set
    pub fn has_option(&self, key: &str) -> bool {
        self.option_list().is_some_and(|ol| ol.has_option(key))
    }

    /// The name of the secondary source tarball
    pub fn component(&self) -> Option<String> {
        self.get_option("component")
    }

    /// Component type
    pub fn ctype(&self) -> Result<Option<ComponentType>, crate::types::ParseError> {
        self.get_option("ctype").map(|s| s.parse()).transpose()
    }

    /// Compression method
    pub fn compression(&self) -> Result<Option<Compression>, crate::types::ParseError> {
        self.get_option("compression")
            .map(|s| s.parse())
            .transpose()
    }

    /// Repack the tarball
    pub fn repack(&self) -> bool {
        self.has_option("repack")
    }

    /// Repack suffix
    pub fn repacksuffix(&self) -> Option<String> {
        self.get_option("repacksuffix")
    }

    /// Retrieve the mode of the watch file entry.
    pub fn mode(&self) -> Result<Mode, crate::types::ParseError> {
        Ok(self
            .get_option("mode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the git pretty mode
    pub fn pretty(&self) -> Result<Pretty, crate::types::ParseError> {
        Ok(self
            .get_option("pretty")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Set the date string used by the pretty option to an arbitrary format as an optional
    /// opts argument when the matching-pattern is HEAD or heads/branch for git mode.
    pub fn date(&self) -> String {
        self.get_option("date").unwrap_or_else(|| "%Y%m%d".into())
    }

    /// Return the git export mode
    pub fn gitexport(&self) -> Result<GitExport, crate::types::ParseError> {
        Ok(self
            .get_option("gitexport")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the git mode
    pub fn gitmode(&self) -> Result<GitMode, crate::types::ParseError> {
        Ok(self
            .get_option("gitmode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the pgp mode
    pub fn pgpmode(&self) -> Result<PgpMode, crate::types::ParseError> {
        Ok(self
            .get_option("pgpmode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the search mode
    pub fn searchmode(&self) -> Result<SearchMode, crate::types::ParseError> {
        Ok(self
            .get_option("searchmode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the decompression mode
    pub fn decompress(&self) -> bool {
        self.has_option("decompress")
    }

    /// Whether to disable all site specific special case code such as URL director uses and page
    /// content alterations.
    pub fn bare(&self) -> bool {
        self.has_option("bare")
    }

    /// Set the user-agent string used to contact the HTTP(S) server as user-agent-string. (persistent)
    pub fn user_agent(&self) -> Option<String> {
        self.get_option("user-agent")
    }

    /// Use PASV mode for the FTP connection.
    pub fn passive(&self) -> Option<bool> {
        if self.has_option("passive") || self.has_option("pasv") {
            Some(true)
        } else if self.has_option("active") || self.has_option("nopasv") {
            Some(false)
        } else {
            None
        }
    }

    /// Add the extra options to use with the unzip command, such as -a, -aa, and -b, when executed
    /// by mk-origtargz.
    pub fn unzipoptions(&self) -> Option<String> {
        self.get_option("unzipopt")
    }

    /// Normalize the downloaded web page string.
    pub fn dversionmangle(&self) -> Option<String> {
        self.get_option("dversionmangle")
            .or_else(|| self.get_option("versionmangle"))
    }

    /// Normalize the directory path string matching the regex in a set of parentheses of
    /// http://URL as the sortable version index string.  This is used
    /// as the directory path sorting index only.
    pub fn dirversionmangle(&self) -> Option<String> {
        self.get_option("dirversionmangle")
    }

    /// Normalize the downloaded web page string.
    pub fn pagemangle(&self) -> Option<String> {
        self.get_option("pagemangle")
    }

    /// Normalize the candidate upstream version strings extracted from hrefs in the
    /// source of the web page.  This is used as the version sorting index when selecting the
    /// latest upstream version.
    pub fn uversionmangle(&self) -> Option<String> {
        self.get_option("uversionmangle")
            .or_else(|| self.get_option("versionmangle"))
    }

    /// Syntactic shorthand for uversionmangle=rules, dversionmangle=rules
    pub fn versionmangle(&self) -> Option<String> {
        self.get_option("versionmangle")
    }

    /// Convert the selected upstream tarball href string from the percent-encoded hexadecimal
    /// string to the decoded normal URL  string  for  obfuscated
    /// web sites.  Only percent-encoding is available and it is decoded with
    /// s/%([A-Fa-f\d]{2})/chr hex $1/eg.
    pub fn hrefdecode(&self) -> bool {
        self.get_option("hrefdecode").is_some()
    }

    /// Convert the selected upstream tarball href string into the accessible URL for obfuscated
    /// web sites.  This is run after hrefdecode.
    pub fn downloadurlmangle(&self) -> Option<String> {
        self.get_option("downloadurlmangle")
    }

    /// Generate the upstream tarball filename from the selected href string if matching-pattern
    /// can extract the latest upstream version <uversion> from the  selected  href  string.
    /// Otherwise, generate the upstream tarball filename from its full URL string and set the
    /// missing <uversion> from the generated upstream tarball filename.
    ///
    /// Without this option, the default upstream tarball filename is generated by taking the last
    /// component of the URL and  removing everything  after any '?' or '#'.
    pub fn filenamemangle(&self) -> Option<String> {
        self.get_option("filenamemangle")
    }

    /// Generate the candidate upstream signature file URL string from the upstream tarball URL.
    pub fn pgpsigurlmangle(&self) -> Option<String> {
        self.get_option("pgpsigurlmangle")
    }

    /// Generate the version string <oversion> of the source tarball <spkg>_<oversion>.orig.tar.gz
    /// from <uversion>.  This should be used to add a suffix such as +dfsg to a MUT package.
    pub fn oversionmangle(&self) -> Option<String> {
        self.get_option("oversionmangle")
    }

    /// Returns options set
    pub fn opts(&self) -> std::collections::HashMap<String, String> {
        let mut options = std::collections::HashMap::new();

        if let Some(ol) = self.option_list() {
            for opt in ol.children() {
                let key = opt.key();
                let value = opt.value();
                if let (Some(key), Some(value)) = (key, value) {
                    options.insert(key.to_string(), value.to_string());
                }
            }
        }

        options
    }

    fn items(&self) -> impl Iterator<Item = String> + '_ {
        self.0.children_with_tokens().filter_map(|it| match it {
            SyntaxElement::Token(token) => {
                if token.kind() == VALUE || token.kind() == KEY {
                    Some(token.text().to_string())
                } else {
                    None
                }
            }
            _ => None,
        })
    }

    /// Returns the URL of the entry.
    pub fn url(&self) -> String {
        self.items().next().unwrap_or_default()
    }

    /// Returns the matching pattern of the entry.
    pub fn matching_pattern(&self) -> Option<String> {
        self.items().nth(1)
    }

    /// Returns the version policy
    pub fn version(&self) -> Result<Option<crate::VersionPolicy>, crate::types::ParseError> {
        self.items().nth(2).map(|it| it.parse()).transpose()
    }

    /// Returns the script of the entry.
    pub fn script(&self) -> Option<String> {
        self.items().nth(3)
    }

    /// Replace all substitutions and return the resulting URL.
    pub fn format_url(
        &self,
        package: impl FnOnce() -> String,
    ) -> Result<url::Url, url::ParseError> {
        subst(self.url().as_str(), package).parse()
    }
}

const SUBSTITUTIONS: &[(&str, &str)] = &[
    // This is substituted with the source package name found in the first line
    // of the debian/changelog file.
    // "@PACKAGE@": None,
    // This is substituted by the legal upstream version regex (capturing).
    ("@ANY_VERSION@", r"[-_]?(\d[\-+\.:\~\da-zA-Z]*)"),
    // This is substituted by the typical archive file extension regex
    // (non-capturing).
    (
        "@ARCHIVE_EXT@",
        r"(?i)\.(?:tar\.xz|tar\.bz2|tar\.gz|zip|tgz|tbz|txz)",
    ),
    // This is substituted by the typical signature file extension regex
    // (non-capturing).
    (
        "@SIGNATURE_EXT@",
        r"(?i)\.(?:tar\.xz|tar\.bz2|tar\.gz|zip|tgz|tbz|txz)\.(?:asc|pgp|gpg|sig|sign)",
    ),
    // This is substituted by the typical Debian extension regexp (capturing).
    ("@DEB_EXT@", r"[\+~](debian|dfsg|ds|deb)(\.)?(\d+)?$"),
];

pub fn subst(text: &str, package: impl FnOnce() -> String) -> String {
    // Early return if no substitutions are needed
    if !text.contains('@') {
        return text.to_string();
    }

    // Apply all substitutions in a single pass using fold
    let result = SUBSTITUTIONS
        .iter()
        .fold(text.to_string(), |acc, (pattern, replacement)| {
            acc.replace(pattern, replacement)
        });

    // Handle @PACKAGE@ substitution if needed
    if result.contains("@PACKAGE@") {
        let package_name = package();
        result.replace("@PACKAGE@", &package_name)
    } else {
        result
    }
}

#[test]
fn test_subst() {
    assert_eq!(
        subst("@ANY_VERSION@", || unreachable!()),
        r"[-_]?(\d[\-+\.:\~\da-zA-Z]*)"
    );
    assert_eq!(subst("@PACKAGE@", || "dulwich".to_string()), "dulwich");
}

impl OptionList {
    fn children(&self) -> impl Iterator<Item = _Option> + '_ {
        self.0.children().filter_map(_Option::cast)
    }

    pub fn has_option(&self, key: &str) -> bool {
        self.children().any(|it| it.key().as_deref() == Some(key))
    }

    pub fn get_option(&self, key: &str) -> Option<String> {
        self.children().find_map(|child| {
            if child.key().as_deref() == Some(key) {
                child.value()
            } else {
                None
            }
        })
    }
}

impl _Option {
    /// Returns the key of the option.
    pub fn key(&self) -> Option<String> {
        self.0.children_with_tokens().find_map(|it| match it {
            SyntaxElement::Token(token) => {
                if token.kind() == KEY {
                    Some(token.text().to_string())
                } else {
                    None
                }
            }
            _ => None,
        })
    }

    /// Returns the value of the option.
    pub fn value(&self) -> Option<String> {
        self.0
            .children_with_tokens()
            .filter_map(|it| match it {
                SyntaxElement::Token(token) => {
                    if token.kind() == VALUE || token.kind() == KEY {
                        Some(token.text().to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .nth(1)
    }
}

#[test]
fn test_parse_v1() {
    const WATCHV1: &str = r#"version=4
opts=bare,filenamemangle=s/.+\/v?(\d\S+)\.tar\.gz/syncthing-gtk-$1\.tar\.gz/ \
  https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
"#;
    let parsed = parse(WATCHV1);
    //assert_eq!(parsed.errors, Vec::<String>::new());
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r#"ROOT@0..161
  VERSION@0..10
    KEY@0..7 "version"
    EQUALS@7..8 "="
    VALUE@8..9 "4"
    NEWLINE@9..10 "\n"
  ENTRY@10..161
    OPTS_LIST@10..86
      KEY@10..14 "opts"
      EQUALS@14..15 "="
      OPTION@15..19
        KEY@15..19 "bare"
      COMMA@19..20 ","
      OPTION@20..86
        KEY@20..34 "filenamemangle"
        EQUALS@34..35 "="
        VALUE@35..86 "s/.+\\/v?(\\d\\S+)\\.tar\\ ..."
    WHITESPACE@86..87 " "
    CONTINUATION@87..89 "\\\n"
    WHITESPACE@89..91 "  "
    VALUE@91..138 "https://github.com/sy ..."
    WHITESPACE@138..139 " "
    VALUE@139..160 ".*/v?(\\d\\S+)\\.tar\\.gz"
    NEWLINE@160..161 "\n"
"#
    );

    let root = parsed.root();
    assert_eq!(root.version(), 4);
    let entries = root.entries().collect::<Vec<_>>();
    assert_eq!(entries.len(), 1);
    let entry = &entries[0];
    assert_eq!(
        entry.url(),
        "https://github.com/syncthing/syncthing-gtk/tags"
    );
    assert_eq!(
        entry.matching_pattern(),
        Some(".*/v?(\\d\\S+)\\.tar\\.gz".into())
    );
    assert_eq!(entry.version(), Ok(None));
    assert_eq!(entry.script(), None);

    assert_eq!(node.text(), WATCHV1);
}

#[test]
fn test_parse_v2() {
    let parsed = parse(
        r#"version=4
https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
# comment
"#,
    );
    assert_eq!(parsed.errors, Vec::<String>::new());
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r###"ROOT@0..90
  VERSION@0..10
    KEY@0..7 "version"
    EQUALS@7..8 "="
    VALUE@8..9 "4"
    NEWLINE@9..10 "\n"
  ENTRY@10..80
    VALUE@10..57 "https://github.com/sy ..."
    WHITESPACE@57..58 " "
    VALUE@58..79 ".*/v?(\\d\\S+)\\.tar\\.gz"
    NEWLINE@79..80 "\n"
  COMMENT@80..89 "# comment"
  NEWLINE@89..90 "\n"
"###
    );

    let root = parsed.root();
    assert_eq!(root.version(), 4);
    let entries = root.entries().collect::<Vec<_>>();
    assert_eq!(entries.len(), 1);
    let entry = &entries[0];
    assert_eq!(
        entry.url(),
        "https://github.com/syncthing/syncthing-gtk/tags"
    );
    assert_eq!(
        entry.format_url(|| "syncthing-gtk".to_string()).unwrap(),
        "https://github.com/syncthing/syncthing-gtk/tags"
            .parse()
            .unwrap()
    );
}

#[test]
fn test_parse_v3() {
    let parsed = parse(
        r#"version=4
https://github.com/syncthing/@PACKAGE@/tags .*/v?(\d\S+)\.tar\.gz
# comment
"#,
    );
    assert_eq!(parsed.errors, Vec::<String>::new());
    let root = parsed.root();
    assert_eq!(root.version(), 4);
    let entries = root.entries().collect::<Vec<_>>();
    assert_eq!(entries.len(), 1);
    let entry = &entries[0];
    assert_eq!(entry.url(), "https://github.com/syncthing/@PACKAGE@/tags");
    assert_eq!(
        entry.format_url(|| "syncthing-gtk".to_string()).unwrap(),
        "https://github.com/syncthing/syncthing-gtk/tags"
            .parse()
            .unwrap()
    );
}

#[test]
fn test_thread_safe_parsing() {
    let text = r#"version=4
https://github.com/example/example/tags example-(.*)\.tar\.gz
"#;

    let parsed = parse_watch_file(text);
    assert!(parsed.is_ok());
    assert_eq!(parsed.errors().len(), 0);

    // Test that we can get the AST from the parse result
    let watchfile = parsed.tree();
    assert_eq!(watchfile.version(), 4);
    let entries: Vec<_> = watchfile.entries().collect();
    assert_eq!(entries.len(), 1);
}

#[test]
fn test_parse_clone_and_eq() {
    let text = r#"version=4
https://github.com/example/example/tags example-(.*)\.tar\.gz
"#;

    let parsed1 = parse_watch_file(text);
    let parsed2 = parsed1.clone();

    // Test that cloned parse results are equal
    assert_eq!(parsed1, parsed2);

    // Test that the AST nodes are also cloneable
    let watchfile1 = parsed1.tree();
    let watchfile2 = watchfile1.clone();
    assert_eq!(watchfile1, watchfile2);
}

#[test]
fn test_parse_v4() {
    let cl: super::WatchFile = r#"version=4
opts=repack,compression=xz,dversionmangle=s/\+ds//,repacksuffix=+ds \
    https://github.com/example/example-cat/tags \
        (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    .parse()
    .unwrap();
    assert_eq!(cl.version(), 4);
    let entries = cl.entries().collect::<Vec<_>>();
    assert_eq!(entries.len(), 1);
    let entry = &entries[0];
    assert_eq!(entry.url(), "https://github.com/example/example-cat/tags");
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );
    assert!(entry.repack());
    assert_eq!(entry.compression(), Ok(Some(Compression::Xz)));
    assert_eq!(entry.dversionmangle(), Some("s/\\+ds//".into()));
    assert_eq!(entry.repacksuffix(), Some("+ds".into()));
    assert_eq!(entry.script(), Some("uupdate".into()));
    assert_eq!(
        entry.format_url(|| "example-cat".to_string()).unwrap(),
        "https://github.com/example/example-cat/tags"
            .parse()
            .unwrap()
    );
    assert_eq!(entry.version(), Ok(Some(VersionPolicy::Debian)));
}

#[test]
fn test_git_mode() {
    let text = r#"version=3
opts="mode=git, gitmode=shallow, pgpmode=gittag" \
https://git.kernel.org/pub/scm/linux/kernel/git/firmware/linux-firmware.git \
refs/tags/(.*) debian
"#;
    let parsed = parse(text);
    assert_eq!(parsed.errors, Vec::<String>::new());
    let cl = parsed.root();
    assert_eq!(cl.version(), 3);
    let entries = cl.entries().collect::<Vec<_>>();
    assert_eq!(entries.len(), 1);
    let entry = &entries[0];
    assert_eq!(
        entry.url(),
        "https://git.kernel.org/pub/scm/linux/kernel/git/firmware/linux-firmware.git"
    );
    assert_eq!(entry.matching_pattern(), Some("refs/tags/(.*)".into()));
    assert_eq!(entry.version(), Ok(Some(VersionPolicy::Debian)));
    assert_eq!(entry.script(), None);
    assert_eq!(entry.gitmode(), Ok(GitMode::Shallow));
    assert_eq!(entry.pgpmode(), Ok(PgpMode::GitTag));
    assert_eq!(entry.mode(), Ok(Mode::Git));
}

#[test]
fn test_parse_quoted() {
    const WATCHV1: &str = r#"version=4
opts="bare, filenamemangle=blah" \
  https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
"#;
    let parsed = parse(WATCHV1);
    //assert_eq!(parsed.errors, Vec::<String>::new());
    let node = parsed.syntax();

    let root = parsed.root();
    assert_eq!(root.version(), 4);
    let entries = root.entries().collect::<Vec<_>>();
    assert_eq!(entries.len(), 1);
    let entry = &entries[0];

    assert_eq!(
        entry.url(),
        "https://github.com/syncthing/syncthing-gtk/tags"
    );
    assert_eq!(
        entry.matching_pattern(),
        Some(".*/v?(\\d\\S+)\\.tar\\.gz".into())
    );
    assert_eq!(entry.version(), Ok(None));
    assert_eq!(entry.script(), None);

    assert_eq!(node.text(), WATCHV1);
}

// Trait implementations for formats 1-4

impl crate::traits::WatchFileFormat for WatchFile {
    type Entry = Entry;

    fn version(&self) -> u32 {
        self.version()
    }

    fn entries(&self) -> Box<dyn Iterator<Item = Self::Entry> + '_> {
        Box::new(WatchFile::entries(self))
    }

    fn to_string(&self) -> String {
        ToString::to_string(self)
    }
}

impl crate::traits::WatchEntry for Entry {
    fn url(&self) -> String {
        Entry::url(self)
    }

    fn matching_pattern(&self) -> Option<String> {
        Entry::matching_pattern(self)
    }

    fn version_policy(&self) -> Result<Option<crate::VersionPolicy>, crate::types::ParseError> {
        Entry::version(self)
    }

    fn script(&self) -> Option<String> {
        Entry::script(self)
    }

    fn get_option(&self, key: &str) -> Option<String> {
        Entry::get_option(self, key)
    }

    fn has_option(&self, key: &str) -> bool {
        Entry::has_option(self, key)
    }
}
