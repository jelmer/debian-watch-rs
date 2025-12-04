use crate::lex::lex;
use crate::types::*;
use crate::SyntaxKind;
use crate::SyntaxKind::*;
use crate::DEFAULT_VERSION;
use std::marker::PhantomData;
use std::str::FromStr;

#[cfg(feature = "discover")]
use crate::discover::Discover;

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
pub(crate) enum Lang {}
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
    pub(crate) fn new(green: GreenNode, errors: Vec<String>) -> Self {
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
        WatchFile::cast(SyntaxNode::new_root_mut(self.green.clone()))
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
                    // Wrap each field in its appropriate node
                    match i {
                        0 => {
                            // URL
                            self.builder.start_node(URL.into());
                            self.bump();
                            self.builder.finish_node();
                        }
                        1 => {
                            // Matching pattern
                            self.builder.start_node(MATCHING_PATTERN.into());
                            self.bump();
                            self.builder.finish_node();
                        }
                        2 => {
                            // Version policy
                            self.builder.start_node(VERSION_POLICY.into());
                            self.bump();
                            self.builder.finish_node();
                        }
                        3 => {
                            // Script
                            self.builder.start_node(SCRIPT.into());
                            self.bump();
                            self.builder.finish_node();
                        }
                        _ => {
                            self.bump();
                        }
                    }
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
                        self.builder.start_node(OPTION_SEPARATOR.into());
                        self.bump();
                        self.builder.finish_node();
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
            // Skip any leading comments/whitespace/newlines before version
            while self.current() == Some(WHITESPACE)
                || self.current() == Some(CONTINUATION)
                || self.current() == Some(COMMENT)
                || self.current() == Some(NEWLINE)
            {
                self.bump();
            }
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
        SyntaxNode::new_root_mut(self.green_node.clone())
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
ast_node!(_Option, OPTION);
ast_node!(Url, URL);
ast_node!(MatchingPattern, MATCHING_PATTERN);
ast_node!(VersionPolicyNode, VERSION_POLICY);
ast_node!(ScriptNode, SCRIPT);

// OptionList is manually defined to have a custom Debug impl
#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
/// A node in the syntax tree for OptionList
pub struct OptionList(SyntaxNode);

impl OptionList {
    #[allow(unused)]
    fn cast(node: SyntaxNode) -> Option<Self> {
        if node.kind() == OPTS_LIST {
            Some(Self(node))
        } else {
            None
        }
    }
}

impl std::fmt::Display for OptionList {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0.text())
    }
}

impl WatchFile {
    /// Access the underlying syntax node (needed for conversion)
    pub(crate) fn syntax(&self) -> &SyntaxNode {
        &self.0
    }

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
        WatchFile(SyntaxNode::new_root_mut(builder.finish()))
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

    /// Set the version of the watch file.
    pub fn set_version(&mut self, new_version: u32) {
        // Build the new version node
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(VERSION.into());
        builder.token(KEY.into(), "version");
        builder.token(EQUALS.into(), "=");
        builder.token(VALUE.into(), new_version.to_string().as_str());
        builder.token(NEWLINE.into(), "\n");
        builder.finish_node();
        let new_version_green = builder.finish();

        // Create a syntax node (splice_children will detach and reattach it)
        let new_version_node = SyntaxNode::new_root_mut(new_version_green);

        // Find existing version node if any
        let version_pos = self.0.children().position(|child| child.kind() == VERSION);

        if let Some(pos) = version_pos {
            // Replace existing version node
            self.0
                .splice_children(pos..pos + 1, vec![new_version_node.into()]);
        } else {
            // Insert version node at the beginning
            self.0.splice_children(0..0, vec![new_version_node.into()]);
        }
    }

    /// Discover releases for all entries in the watch file (async version)
    ///
    /// Fetches URLs and searches for version matches for all entries.
    /// Requires the 'discover' feature.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// # use debian_watch::WatchFile;
    /// # async fn example() {
    /// let wf: WatchFile = r#"version=4
    /// https://example.com/releases/ .*/v?(\d+\.\d+)\.tar\.gz
    /// "#.parse().unwrap();
    /// let all_releases = wf.uscan(|| "mypackage".to_string()).await.unwrap();
    /// for (entry_idx, releases) in all_releases.iter().enumerate() {
    ///     println!("Entry {}: {} releases found", entry_idx, releases.len());
    /// }
    /// # }
    /// ```
    #[cfg(feature = "discover")]
    pub async fn uscan(
        &self,
        package: impl Fn() -> String + Send + Sync,
    ) -> Result<Vec<Vec<crate::Release>>, Box<dyn std::error::Error>> {
        let mut all_releases = Vec::new();

        for entry in self.entries() {
            let releases = entry.discover(|| package()).await?;
            all_releases.push(releases);
        }

        Ok(all_releases)
    }

    /// Discover releases for all entries in the watch file (blocking version)
    ///
    /// Fetches URLs and searches for version matches for all entries.
    /// Requires both 'discover' and 'blocking' features.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// # use debian_watch::WatchFile;
    /// let wf: WatchFile = r#"version=4
    /// https://example.com/releases/ .*/v?(\d+\.\d+)\.tar\.gz
    /// "#.parse().unwrap();
    /// let all_releases = wf.uscan_blocking(|| "mypackage".to_string()).unwrap();
    /// for (entry_idx, releases) in all_releases.iter().enumerate() {
    ///     println!("Entry {}: {} releases found", entry_idx, releases.len());
    /// }
    /// ```
    #[cfg(all(feature = "discover", feature = "blocking"))]
    pub fn uscan_blocking(
        &self,
        package: impl Fn() -> String,
    ) -> Result<Vec<Vec<crate::Release>>, Box<dyn std::error::Error>> {
        let mut all_releases = Vec::new();

        for entry in self.entries() {
            let releases = entry.discover_blocking(|| package())?;
            all_releases.push(releases);
        }

        Ok(all_releases)
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
    /// Access the underlying syntax node (needed for conversion)
    pub(crate) fn syntax(&self) -> &SyntaxNode {
        &self.0
    }

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
    pub fn ctype(&self) -> Result<Option<ComponentType>, ()> {
        self.try_ctype().map_err(|_| ())
    }

    /// Component type with detailed error information
    pub fn try_ctype(&self) -> Result<Option<ComponentType>, crate::types::ParseError> {
        self.get_option("ctype").map(|s| s.parse()).transpose()
    }

    /// Compression method
    pub fn compression(&self) -> Result<Option<Compression>, ()> {
        self.try_compression().map_err(|_| ())
    }

    /// Compression method with detailed error information
    pub fn try_compression(&self) -> Result<Option<Compression>, crate::types::ParseError> {
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
    pub fn mode(&self) -> Result<Mode, ()> {
        self.try_mode().map_err(|_| ())
    }

    /// Retrieve the mode of the watch file entry with detailed error information.
    pub fn try_mode(&self) -> Result<Mode, crate::types::ParseError> {
        Ok(self
            .get_option("mode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the git pretty mode
    pub fn pretty(&self) -> Result<Pretty, ()> {
        self.try_pretty().map_err(|_| ())
    }

    /// Return the git pretty mode with detailed error information
    pub fn try_pretty(&self) -> Result<Pretty, crate::types::ParseError> {
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
    pub fn gitexport(&self) -> Result<GitExport, ()> {
        self.try_gitexport().map_err(|_| ())
    }

    /// Return the git export mode with detailed error information
    pub fn try_gitexport(&self) -> Result<GitExport, crate::types::ParseError> {
        Ok(self
            .get_option("gitexport")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the git mode
    pub fn gitmode(&self) -> Result<GitMode, ()> {
        self.try_gitmode().map_err(|_| ())
    }

    /// Return the git mode with detailed error information
    pub fn try_gitmode(&self) -> Result<GitMode, crate::types::ParseError> {
        Ok(self
            .get_option("gitmode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the pgp mode
    pub fn pgpmode(&self) -> Result<PgpMode, ()> {
        self.try_pgpmode().map_err(|_| ())
    }

    /// Return the pgp mode with detailed error information
    pub fn try_pgpmode(&self) -> Result<PgpMode, crate::types::ParseError> {
        Ok(self
            .get_option("pgpmode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the search mode
    pub fn searchmode(&self) -> Result<SearchMode, ()> {
        self.try_searchmode().map_err(|_| ())
    }

    /// Return the search mode with detailed error information
    pub fn try_searchmode(&self) -> Result<SearchMode, crate::types::ParseError> {
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

    /// Apply uversionmangle to a version string
    ///
    /// # Examples
    ///
    /// ```
    /// # use debian_watch::WatchFile;
    /// let wf: WatchFile = r#"version=4
    /// opts=uversionmangle=s/\+ds// https://example.com/ .*
    /// "#.parse().unwrap();
    /// let entry = wf.entries().next().unwrap();
    /// assert_eq!(entry.apply_uversionmangle("1.0+ds").unwrap(), "1.0");
    /// ```
    pub fn apply_uversionmangle(
        &self,
        version: &str,
    ) -> Result<String, crate::mangle::MangleError> {
        if let Some(vm) = self.uversionmangle() {
            crate::mangle::apply_mangle(&vm, version)
        } else {
            Ok(version.to_string())
        }
    }

    /// Apply dversionmangle to a version string
    ///
    /// # Examples
    ///
    /// ```
    /// # use debian_watch::WatchFile;
    /// let wf: WatchFile = r#"version=4
    /// opts=dversionmangle=s/\+dfsg$// https://example.com/ .*
    /// "#.parse().unwrap();
    /// let entry = wf.entries().next().unwrap();
    /// assert_eq!(entry.apply_dversionmangle("1.0+dfsg").unwrap(), "1.0");
    /// ```
    pub fn apply_dversionmangle(
        &self,
        version: &str,
    ) -> Result<String, crate::mangle::MangleError> {
        if let Some(vm) = self.dversionmangle() {
            crate::mangle::apply_mangle(&vm, version)
        } else {
            Ok(version.to_string())
        }
    }

    /// Apply oversionmangle to a version string
    ///
    /// # Examples
    ///
    /// ```
    /// # use debian_watch::WatchFile;
    /// let wf: WatchFile = r#"version=4
    /// opts=oversionmangle=s/$/-1/ https://example.com/ .*
    /// "#.parse().unwrap();
    /// let entry = wf.entries().next().unwrap();
    /// assert_eq!(entry.apply_oversionmangle("1.0").unwrap(), "1.0-1");
    /// ```
    pub fn apply_oversionmangle(
        &self,
        version: &str,
    ) -> Result<String, crate::mangle::MangleError> {
        if let Some(vm) = self.oversionmangle() {
            crate::mangle::apply_mangle(&vm, version)
        } else {
            Ok(version.to_string())
        }
    }

    /// Apply dirversionmangle to a directory path string
    ///
    /// # Examples
    ///
    /// ```
    /// # use debian_watch::WatchFile;
    /// let wf: WatchFile = r#"version=4
    /// opts=dirversionmangle=s/v(\d)/$1/ https://example.com/ .*
    /// "#.parse().unwrap();
    /// let entry = wf.entries().next().unwrap();
    /// assert_eq!(entry.apply_dirversionmangle("v1.0").unwrap(), "1.0");
    /// ```
    pub fn apply_dirversionmangle(
        &self,
        version: &str,
    ) -> Result<String, crate::mangle::MangleError> {
        if let Some(vm) = self.dirversionmangle() {
            crate::mangle::apply_mangle(&vm, version)
        } else {
            Ok(version.to_string())
        }
    }

    /// Apply filenamemangle to a URL or filename string
    ///
    /// # Examples
    ///
    /// ```
    /// # use debian_watch::WatchFile;
    /// let wf: WatchFile = r#"version=4
    /// opts=filenamemangle=s/.+\/v?(\d\S+)\.tar\.gz/mypackage-$1.tar.gz/ https://example.com/ .*
    /// "#.parse().unwrap();
    /// let entry = wf.entries().next().unwrap();
    /// assert_eq!(
    ///     entry.apply_filenamemangle("https://example.com/v1.0.tar.gz").unwrap(),
    ///     "mypackage-1.0.tar.gz"
    /// );
    /// ```
    pub fn apply_filenamemangle(&self, url: &str) -> Result<String, crate::mangle::MangleError> {
        if let Some(vm) = self.filenamemangle() {
            crate::mangle::apply_mangle(&vm, url)
        } else {
            Ok(url.to_string())
        }
    }

    /// Apply pagemangle to page content bytes
    ///
    /// # Examples
    ///
    /// ```
    /// # use debian_watch::WatchFile;
    /// let wf: WatchFile = r#"version=4
    /// opts=pagemangle=s/&amp;/&/g https://example.com/ .*
    /// "#.parse().unwrap();
    /// let entry = wf.entries().next().unwrap();
    /// assert_eq!(
    ///     entry.apply_pagemangle(b"foo &amp; bar").unwrap(),
    ///     b"foo & bar"
    /// );
    /// ```
    pub fn apply_pagemangle(&self, page: &[u8]) -> Result<Vec<u8>, crate::mangle::MangleError> {
        if let Some(vm) = self.pagemangle() {
            let page_str = String::from_utf8_lossy(page);
            let mangled = crate::mangle::apply_mangle(&vm, &page_str)?;
            Ok(mangled.into_bytes())
        } else {
            Ok(page.to_vec())
        }
    }

    /// Apply downloadurlmangle to a URL string
    ///
    /// # Examples
    ///
    /// ```
    /// # use debian_watch::WatchFile;
    /// let wf: WatchFile = r#"version=4
    /// opts=downloadurlmangle=s|/archive/|/download/| https://example.com/ .*
    /// "#.parse().unwrap();
    /// let entry = wf.entries().next().unwrap();
    /// assert_eq!(
    ///     entry.apply_downloadurlmangle("https://example.com/archive/file.tar.gz").unwrap(),
    ///     "https://example.com/download/file.tar.gz"
    /// );
    /// ```
    pub fn apply_downloadurlmangle(&self, url: &str) -> Result<String, crate::mangle::MangleError> {
        if let Some(vm) = self.downloadurlmangle() {
            crate::mangle::apply_mangle(&vm, url)
        } else {
            Ok(url.to_string())
        }
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
            SyntaxElement::Node(node) => {
                // Extract values from entry field nodes
                match node.kind() {
                    URL => Url::cast(node).map(|n| n.url()),
                    MATCHING_PATTERN => MatchingPattern::cast(node).map(|n| n.pattern()),
                    VERSION_POLICY => VersionPolicyNode::cast(node).map(|n| n.policy()),
                    SCRIPT => ScriptNode::cast(node).map(|n| n.script()),
                    _ => None,
                }
            }
        })
    }

    /// Returns the URL of the entry.
    pub fn url(&self) -> String {
        self.0
            .children()
            .find_map(Url::cast)
            .map(|it| it.url())
            .unwrap_or_else(|| {
                // Fallback for entries without URL node (shouldn't happen with new parser)
                self.items().next().unwrap()
            })
    }

    /// Returns the matching pattern of the entry.
    pub fn matching_pattern(&self) -> Option<String> {
        self.0
            .children()
            .find_map(MatchingPattern::cast)
            .map(|it| it.pattern())
            .or_else(|| {
                // Fallback for entries without MATCHING_PATTERN node
                self.items().nth(1)
            })
    }

    /// Returns the version policy
    pub fn version(&self) -> Result<Option<crate::VersionPolicy>, String> {
        self.0
            .children()
            .find_map(VersionPolicyNode::cast)
            .map(|it| it.policy().parse())
            .transpose()
            .map_err(|e: crate::types::ParseError| e.to_string())
            .or_else(|_e| {
                // Fallback for entries without VERSION_POLICY node
                self.items().nth(2).map(|it| it.parse()).transpose().map_err(|e: crate::types::ParseError| e.to_string())
            })
    }

    /// Returns the script of the entry.
    pub fn script(&self) -> Option<String> {
        self.0
            .children()
            .find_map(ScriptNode::cast)
            .map(|it| it.script())
            .or_else(|| {
                // Fallback for entries without SCRIPT node
                self.items().nth(3)
            })
    }

    /// Replace all substitutions and return the resulting URL.
    pub fn format_url(&self, package: impl FnOnce() -> String) -> url::Url {
        subst(self.url().as_str(), package).parse().unwrap()
    }

    /// Set the URL of the entry.
    pub fn set_url(&mut self, new_url: &str) {
        // Build the new URL node
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(URL.into());
        builder.token(VALUE.into(), new_url);
        builder.finish_node();
        let new_url_green = builder.finish();

        // Create a syntax node (splice_children will detach and reattach it)
        let new_url_node = SyntaxNode::new_root_mut(new_url_green);

        // Find existing URL node position (need to use children_with_tokens for correct indexing)
        let url_pos = self
            .0
            .children_with_tokens()
            .position(|child| matches!(child, SyntaxElement::Node(node) if node.kind() == URL));

        if let Some(pos) = url_pos {
            // Replace existing URL node
            self.0
                .splice_children(pos..pos + 1, vec![new_url_node.into()]);
        }
    }

    /// Set the matching pattern of the entry.
    ///
    /// TODO: This currently only replaces an existing matching pattern.
    /// If the entry doesn't have a matching pattern, this method does nothing.
    /// Future implementation should insert the node at the correct position.
    pub fn set_matching_pattern(&mut self, new_pattern: &str) {
        // Build the new MATCHING_PATTERN node
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(MATCHING_PATTERN.into());
        builder.token(VALUE.into(), new_pattern);
        builder.finish_node();
        let new_pattern_green = builder.finish();

        // Create a syntax node (splice_children will detach and reattach it)
        let new_pattern_node = SyntaxNode::new_root_mut(new_pattern_green);

        // Find existing MATCHING_PATTERN node position
        let pattern_pos = self.0.children_with_tokens().position(
            |child| matches!(child, SyntaxElement::Node(node) if node.kind() == MATCHING_PATTERN),
        );

        if let Some(pos) = pattern_pos {
            // Replace existing MATCHING_PATTERN node
            self.0
                .splice_children(pos..pos + 1, vec![new_pattern_node.into()]);
        }
        // TODO: else insert new node after URL
    }

    /// Set the version policy of the entry.
    ///
    /// TODO: This currently only replaces an existing version policy.
    /// If the entry doesn't have a version policy, this method does nothing.
    /// Future implementation should insert the node at the correct position.
    pub fn set_version_policy(&mut self, new_policy: &str) {
        // Build the new VERSION_POLICY node
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(VERSION_POLICY.into());
        // Version policy can be KEY (e.g., "debian") or VALUE
        builder.token(VALUE.into(), new_policy);
        builder.finish_node();
        let new_policy_green = builder.finish();

        // Create a syntax node (splice_children will detach and reattach it)
        let new_policy_node = SyntaxNode::new_root_mut(new_policy_green);

        // Find existing VERSION_POLICY node position
        let policy_pos = self.0.children_with_tokens().position(
            |child| matches!(child, SyntaxElement::Node(node) if node.kind() == VERSION_POLICY),
        );

        if let Some(pos) = policy_pos {
            // Replace existing VERSION_POLICY node
            self.0
                .splice_children(pos..pos + 1, vec![new_policy_node.into()]);
        }
        // TODO: else insert new node after MATCHING_PATTERN (or URL if no pattern)
    }

    /// Set the script of the entry.
    ///
    /// TODO: This currently only replaces an existing script.
    /// If the entry doesn't have a script, this method does nothing.
    /// Future implementation should insert the node at the correct position.
    pub fn set_script(&mut self, new_script: &str) {
        // Build the new SCRIPT node
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(SCRIPT.into());
        // Script can be KEY (e.g., "uupdate") or VALUE
        builder.token(VALUE.into(), new_script);
        builder.finish_node();
        let new_script_green = builder.finish();

        // Create a syntax node (splice_children will detach and reattach it)
        let new_script_node = SyntaxNode::new_root_mut(new_script_green);

        // Find existing SCRIPT node position
        let script_pos = self
            .0
            .children_with_tokens()
            .position(|child| matches!(child, SyntaxElement::Node(node) if node.kind() == SCRIPT));

        if let Some(pos) = script_pos {
            // Replace existing SCRIPT node
            self.0
                .splice_children(pos..pos + 1, vec![new_script_node.into()]);
        }
        // TODO: else insert new node after VERSION_POLICY (or MATCHING_PATTERN/URL if no policy)
    }

    /// Set or update an option value.
    ///
    /// If the option already exists, it will be updated with the new value.
    /// If the option doesn't exist, it will be added to the options list.
    /// If there's no options list, one will be created.
    pub fn set_opt(&mut self, key: &str, value: &str) {
        // Find the OPTS_LIST position in Entry
        let opts_pos = self.0.children_with_tokens().position(
            |child| matches!(child, SyntaxElement::Node(node) if node.kind() == OPTS_LIST),
        );

        if let Some(_opts_idx) = opts_pos {
            if let Some(mut ol) = self.option_list() {
                // Find if the option already exists
                if let Some(mut opt) = ol.find_option(key) {
                    // Update the existing option's value
                    opt.set_value(value);
                    // Mutations should propagate automatically - no need to replace
                } else {
                    // Add new option
                    ol.add_option(key, value);
                    // Mutations should propagate automatically - no need to replace
                }
            }
        } else {
            // Create a new options list
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(OPTS_LIST.into());
            builder.token(KEY.into(), "opts");
            builder.token(EQUALS.into(), "=");
            builder.start_node(OPTION.into());
            builder.token(KEY.into(), key);
            builder.token(EQUALS.into(), "=");
            builder.token(VALUE.into(), value);
            builder.finish_node();
            builder.finish_node();
            let new_opts_green = builder.finish();
            let new_opts_node = SyntaxNode::new_root_mut(new_opts_green);

            // Find position to insert (before URL if it exists, otherwise at start)
            let url_pos = self
                .0
                .children_with_tokens()
                .position(|child| matches!(child, SyntaxElement::Node(node) if node.kind() == URL));

            if let Some(url_idx) = url_pos {
                // Insert options list and a space before the URL
                // Build a parent node containing both space and whitespace to extract from
                let mut combined_builder = GreenNodeBuilder::new();
                combined_builder.start_node(ROOT.into()); // Temporary parent
                combined_builder.token(WHITESPACE.into(), " ");
                combined_builder.finish_node();
                let temp_green = combined_builder.finish();
                let temp_root = SyntaxNode::new_root_mut(temp_green);
                let space_element = temp_root.children_with_tokens().next().unwrap();

                self.0
                    .splice_children(url_idx..url_idx, vec![new_opts_node.into(), space_element]);
            } else {
                self.0.splice_children(0..0, vec![new_opts_node.into()]);
            }
        }
    }

    /// Delete an option.
    ///
    /// Removes the option with the specified key from the options list.
    /// If the option doesn't exist, this method does nothing.
    /// If deleting the option results in an empty options list, the entire
    /// opts= declaration is removed.
    pub fn del_opt(&mut self, key: &str) {
        if let Some(mut ol) = self.option_list() {
            let option_count = ol.0.children().filter(|n| n.kind() == OPTION).count();

            if option_count == 1 && ol.has_option(key) {
                // This is the last option, remove the entire OPTS_LIST from Entry
                let opts_pos = self.0.children().position(|node| node.kind() == OPTS_LIST);

                if let Some(opts_idx) = opts_pos {
                    // Remove the OPTS_LIST
                    self.0.splice_children(opts_idx..opts_idx + 1, vec![]);

                    // Remove any leading whitespace/continuation that was after the OPTS_LIST
                    while self.0.children_with_tokens().next().map_or(false, |e| {
                        matches!(
                            e,
                            SyntaxElement::Token(t) if t.kind() == WHITESPACE || t.kind() == CONTINUATION
                        )
                    }) {
                        self.0.splice_children(0..1, vec![]);
                    }
                }
            } else {
                // Defer to OptionList to remove the option
                ol.remove_option(key);
            }
        }
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

impl std::fmt::Debug for OptionList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OptionList")
            .field("text", &self.0.text().to_string())
            .finish()
    }
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

    /// Returns an iterator over all options as (key, value) pairs
    pub(crate) fn options(&self) -> impl Iterator<Item = (String, String)> + '_ {
        self.children().filter_map(|opt| {
            if let (Some(key), Some(value)) = (opt.key(), opt.value()) {
                Some((key, value))
            } else {
                None
            }
        })
    }

    /// Find an option by key.
    fn find_option(&self, key: &str) -> Option<_Option> {
        self.children()
            .find(|opt| opt.key().as_deref() == Some(key))
    }

    /// Add a new option to the end of the options list.
    fn add_option(&mut self, key: &str, value: &str) {
        let option_count = self.0.children().filter(|n| n.kind() == OPTION).count();

        // Build a structure containing separator (if needed) + option wrapped in a temporary parent
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(ROOT.into()); // Temporary parent

        if option_count > 0 {
            builder.start_node(OPTION_SEPARATOR.into());
            builder.token(COMMA.into(), ",");
            builder.finish_node();
        }

        builder.start_node(OPTION.into());
        builder.token(KEY.into(), key);
        builder.token(EQUALS.into(), "=");
        builder.token(VALUE.into(), value);
        builder.finish_node();

        builder.finish_node(); // Close temporary parent
        let combined_green = builder.finish();

        // Create a temporary root to extract children from
        let temp_root = SyntaxNode::new_root_mut(combined_green);
        let new_children: Vec<_> = temp_root.children_with_tokens().collect();

        let insert_pos = self.0.children_with_tokens().count();
        self.0.splice_children(insert_pos..insert_pos, new_children);
    }

    /// Remove an option by key. Returns true if an option was removed.
    fn remove_option(&mut self, key: &str) -> bool {
        if let Some(mut opt) = self.find_option(key) {
            opt.remove();
            true
        } else {
            false
        }
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

    /// Set the value of the option.
    pub fn set_value(&mut self, new_value: &str) {
        let key = self.key().expect("Option must have a key");

        // Build a new OPTION node with the updated value
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(OPTION.into());
        builder.token(KEY.into(), &key);
        builder.token(EQUALS.into(), "=");
        builder.token(VALUE.into(), new_value);
        builder.finish_node();
        let new_option_green = builder.finish();
        let new_option_node = SyntaxNode::new_root_mut(new_option_green);

        // Replace this option in the parent OptionList
        if let Some(parent) = self.0.parent() {
            let idx = self.0.index();
            parent.splice_children(idx..idx + 1, vec![new_option_node.into()]);
        }
    }

    /// Remove this option and its associated separator from the parent OptionList.
    pub fn remove(&mut self) {
        // Find adjacent separator to remove before detaching this node
        let next_sep = self
            .0
            .next_sibling()
            .filter(|n| n.kind() == OPTION_SEPARATOR);
        let prev_sep = self
            .0
            .prev_sibling()
            .filter(|n| n.kind() == OPTION_SEPARATOR);

        // Detach separator first if it exists
        if let Some(sep) = next_sep {
            sep.detach();
        } else if let Some(sep) = prev_sep {
            sep.detach();
        }

        // Now detach the option itself
        self.0.detach();
    }
}

impl Url {
    /// Returns the URL string.
    pub fn url(&self) -> String {
        self.0
            .children_with_tokens()
            .find_map(|it| match it {
                SyntaxElement::Token(token) => {
                    if token.kind() == VALUE {
                        Some(token.text().to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .unwrap()
    }
}

impl MatchingPattern {
    /// Returns the matching pattern string.
    pub fn pattern(&self) -> String {
        self.0
            .children_with_tokens()
            .find_map(|it| match it {
                SyntaxElement::Token(token) => {
                    if token.kind() == VALUE {
                        Some(token.text().to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .unwrap()
    }
}

impl VersionPolicyNode {
    /// Returns the version policy string.
    pub fn policy(&self) -> String {
        self.0
            .children_with_tokens()
            .find_map(|it| match it {
                SyntaxElement::Token(token) => {
                    // Can be KEY (e.g., "debian") or VALUE
                    if token.kind() == VALUE || token.kind() == KEY {
                        Some(token.text().to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .unwrap()
    }
}

impl ScriptNode {
    /// Returns the script string.
    pub fn script(&self) -> String {
        self.0
            .children_with_tokens()
            .find_map(|it| match it {
                SyntaxElement::Token(token) => {
                    // Can be KEY (e.g., "uupdate") or VALUE
                    if token.kind() == VALUE || token.kind() == KEY {
                        Some(token.text().to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .unwrap()
    }
}

#[test]
fn test_entry_node_structure() {
    // Test that entries properly use the new node types
    let wf: super::WatchFile = r#"version=4
opts=compression=xz https://example.com/releases (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    .parse()
    .unwrap();

    let entry = wf.entries().next().unwrap();

    // Verify URL node exists and works
    assert_eq!(entry.0.children().find(|n| n.kind() == URL).is_some(), true);
    assert_eq!(entry.url(), "https://example.com/releases");

    // Verify MATCHING_PATTERN node exists and works
    assert_eq!(
        entry
            .0
            .children()
            .find(|n| n.kind() == MATCHING_PATTERN)
            .is_some(),
        true
    );
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );

    // Verify VERSION_POLICY node exists and works
    assert_eq!(
        entry
            .0
            .children()
            .find(|n| n.kind() == VERSION_POLICY)
            .is_some(),
        true
    );
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Debian)));

    // Verify SCRIPT node exists and works
    assert_eq!(
        entry.0.children().find(|n| n.kind() == SCRIPT).is_some(),
        true
    );
    assert_eq!(entry.script(), Some("uupdate".into()));
}

#[test]
fn test_entry_node_structure_partial() {
    // Test entry with only URL and pattern (no version or script)
    let wf: super::WatchFile = r#"version=4
https://github.com/example/tags .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let entry = wf.entries().next().unwrap();

    // Should have URL and MATCHING_PATTERN nodes
    assert_eq!(entry.0.children().find(|n| n.kind() == URL).is_some(), true);
    assert_eq!(
        entry
            .0
            .children()
            .find(|n| n.kind() == MATCHING_PATTERN)
            .is_some(),
        true
    );

    // Should NOT have VERSION_POLICY or SCRIPT nodes
    assert_eq!(
        entry
            .0
            .children()
            .find(|n| n.kind() == VERSION_POLICY)
            .is_some(),
        false
    );
    assert_eq!(
        entry.0.children().find(|n| n.kind() == SCRIPT).is_some(),
        false
    );

    // Verify accessors work correctly
    assert_eq!(entry.url(), "https://github.com/example/tags");
    assert_eq!(
        entry.matching_pattern(),
        Some(".*/v?(\\d\\S+)\\.tar\\.gz".into())
    );
    assert_eq!(entry.version(), Ok(None));
    assert_eq!(entry.script(), None);
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
      OPTION_SEPARATOR@19..20
        COMMA@19..20 ","
      OPTION@20..86
        KEY@20..34 "filenamemangle"
        EQUALS@34..35 "="
        VALUE@35..86 "s/.+\\/v?(\\d\\S+)\\.tar\\ ..."
    WHITESPACE@86..87 " "
    CONTINUATION@87..89 "\\\n"
    WHITESPACE@89..91 "  "
    URL@91..138
      VALUE@91..138 "https://github.com/sy ..."
    WHITESPACE@138..139 " "
    MATCHING_PATTERN@139..160
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
    URL@10..57
      VALUE@10..57 "https://github.com/sy ..."
    WHITESPACE@57..58 " "
    MATCHING_PATTERN@58..79
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
        entry.format_url(|| "syncthing-gtk".to_string()),
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
        entry.format_url(|| "syncthing-gtk".to_string()),
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
        entry.format_url(|| "example-cat".to_string()),
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

    fn format_string(&self) -> String {
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
        Entry::version(self).map_err(|e| crate::types::ParseError {
            type_name: "VersionPolicy",
            value: e,
        })
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

#[test]
fn test_set_url() {
    // Test setting URL on a simple entry without options
    let wf: super::WatchFile = r#"version=4
https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(
        entry.url(),
        "https://github.com/syncthing/syncthing-gtk/tags"
    );

    entry.set_url("https://newurl.example.org/path");
    assert_eq!(entry.url(), "https://newurl.example.org/path");
    assert_eq!(
        entry.matching_pattern(),
        Some(".*/v?(\\d\\S+)\\.tar\\.gz".into())
    );

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "https://newurl.example.org/path .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_set_url_with_options() {
    // Test setting URL on an entry with options
    let wf: super::WatchFile = r#"version=4
opts=foo=blah https://foo.com/bar .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.url(), "https://foo.com/bar");
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));

    entry.set_url("https://example.com/baz");
    assert_eq!(entry.url(), "https://example.com/baz");

    // Verify options are preserved
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));
    assert_eq!(
        entry.matching_pattern(),
        Some(".*/v?(\\d\\S+)\\.tar\\.gz".into())
    );

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=foo=blah https://example.com/baz .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_set_url_complex() {
    // Test with a complex watch file with multiple options and continuation
    let wf: super::WatchFile = r#"version=4
opts=bare,filenamemangle=s/.+\/v?(\d\S+)\.tar\.gz/syncthing-gtk-$1\.tar\.gz/ \
  https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(
        entry.url(),
        "https://github.com/syncthing/syncthing-gtk/tags"
    );

    entry.set_url("https://gitlab.com/newproject/tags");
    assert_eq!(entry.url(), "https://gitlab.com/newproject/tags");

    // Verify all options are preserved
    assert!(entry.bare());
    assert_eq!(
        entry.filenamemangle(),
        Some("s/.+\\/v?(\\d\\S+)\\.tar\\.gz/syncthing-gtk-$1\\.tar\\.gz/".into())
    );
    assert_eq!(
        entry.matching_pattern(),
        Some(".*/v?(\\d\\S+)\\.tar\\.gz".into())
    );

    // Verify the exact serialized output preserves structure
    assert_eq!(
        entry.to_string(),
        r#"opts=bare,filenamemangle=s/.+\/v?(\d\S+)\.tar\.gz/syncthing-gtk-$1\.tar\.gz/ \
  https://gitlab.com/newproject/tags .*/v?(\d\S+)\.tar\.gz
"#
    );
}

#[test]
fn test_set_url_with_all_fields() {
    // Test with all fields: options, URL, matching pattern, version, and script
    let wf: super::WatchFile = r#"version=4
opts=repack,compression=xz,dversionmangle=s/\+ds//,repacksuffix=+ds \
    https://github.com/example/example-cat/tags \
        (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.url(), "https://github.com/example/example-cat/tags");
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Debian)));
    assert_eq!(entry.script(), Some("uupdate".into()));

    entry.set_url("https://gitlab.example.org/project/releases");
    assert_eq!(entry.url(), "https://gitlab.example.org/project/releases");

    // Verify all other fields are preserved
    assert!(entry.repack());
    assert_eq!(entry.compression(), Ok(Some(super::Compression::Xz)));
    assert_eq!(entry.dversionmangle(), Some("s/\\+ds//".into()));
    assert_eq!(entry.repacksuffix(), Some("+ds".into()));
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Debian)));
    assert_eq!(entry.script(), Some("uupdate".into()));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        r#"opts=repack,compression=xz,dversionmangle=s/\+ds//,repacksuffix=+ds \
    https://gitlab.example.org/project/releases \
        (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    );
}

#[test]
fn test_set_url_quoted_options() {
    // Test with quoted options
    let wf: super::WatchFile = r#"version=4
opts="bare, filenamemangle=blah" \
  https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(
        entry.url(),
        "https://github.com/syncthing/syncthing-gtk/tags"
    );

    entry.set_url("https://example.org/new/path");
    assert_eq!(entry.url(), "https://example.org/new/path");

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        r#"opts="bare, filenamemangle=blah" \
  https://example.org/new/path .*/v?(\d\S+)\.tar\.gz
"#
    );
}

#[test]
fn test_set_opt_update_existing() {
    // Test updating an existing option
    let wf: super::WatchFile = r#"version=4
opts=foo=blah,bar=baz https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));
    assert_eq!(entry.get_option("bar"), Some("baz".to_string()));

    entry.set_opt("foo", "updated");
    assert_eq!(entry.get_option("foo"), Some("updated".to_string()));
    assert_eq!(entry.get_option("bar"), Some("baz".to_string()));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=foo=updated,bar=baz https://example.com/releases .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_set_opt_add_new() {
    // Test adding a new option to existing options
    let wf: super::WatchFile = r#"version=4
opts=foo=blah https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));
    assert_eq!(entry.get_option("bar"), None);

    entry.set_opt("bar", "baz");
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));
    assert_eq!(entry.get_option("bar"), Some("baz".to_string()));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=foo=blah,bar=baz https://example.com/releases .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_set_opt_create_options_list() {
    // Test creating a new options list when none exists
    let wf: super::WatchFile = r#"version=4
https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.option_list(), None);

    entry.set_opt("compression", "xz");
    assert_eq!(entry.get_option("compression"), Some("xz".to_string()));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=compression=xz https://example.com/releases .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_del_opt_remove_single() {
    // Test removing a single option from multiple options
    let wf: super::WatchFile = r#"version=4
opts=foo=blah,bar=baz,qux=quux https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));
    assert_eq!(entry.get_option("bar"), Some("baz".to_string()));
    assert_eq!(entry.get_option("qux"), Some("quux".to_string()));

    entry.del_opt("bar");
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));
    assert_eq!(entry.get_option("bar"), None);
    assert_eq!(entry.get_option("qux"), Some("quux".to_string()));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=foo=blah,qux=quux https://example.com/releases .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_del_opt_remove_first() {
    // Test removing the first option
    let wf: super::WatchFile = r#"version=4
opts=foo=blah,bar=baz https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    entry.del_opt("foo");
    assert_eq!(entry.get_option("foo"), None);
    assert_eq!(entry.get_option("bar"), Some("baz".to_string()));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=bar=baz https://example.com/releases .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_del_opt_remove_last() {
    // Test removing the last option
    let wf: super::WatchFile = r#"version=4
opts=foo=blah,bar=baz https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    entry.del_opt("bar");
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));
    assert_eq!(entry.get_option("bar"), None);

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=foo=blah https://example.com/releases .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_del_opt_remove_only_option() {
    // Test removing the only option (should remove entire opts list)
    let wf: super::WatchFile = r#"version=4
opts=foo=blah https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.get_option("foo"), Some("blah".to_string()));

    entry.del_opt("foo");
    assert_eq!(entry.get_option("foo"), None);
    assert_eq!(entry.option_list(), None);

    // Verify the exact serialized output (opts should be gone)
    assert_eq!(
        entry.to_string(),
        "https://example.com/releases .*/v?(\\d\\S+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_del_opt_nonexistent() {
    // Test deleting a non-existent option (should do nothing)
    let wf: super::WatchFile = r#"version=4
opts=foo=blah https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    let original = entry.to_string();

    entry.del_opt("nonexistent");
    assert_eq!(entry.to_string(), original);
}

#[test]
fn test_set_opt_multiple_operations() {
    // Test multiple set_opt operations
    let wf: super::WatchFile = r#"version=4
https://example.com/releases .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();

    entry.set_opt("compression", "xz");
    entry.set_opt("repack", "");
    entry.set_opt("dversionmangle", "s/\\+ds//");

    assert_eq!(entry.get_option("compression"), Some("xz".to_string()));
    assert_eq!(
        entry.get_option("dversionmangle"),
        Some("s/\\+ds//".to_string())
    );
}

#[test]
fn test_set_matching_pattern() {
    // Test setting matching pattern on a simple entry
    let wf: super::WatchFile = r#"version=4
https://github.com/example/tags .*/v?(\d\S+)\.tar\.gz
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(
        entry.matching_pattern(),
        Some(".*/v?(\\d\\S+)\\.tar\\.gz".into())
    );

    entry.set_matching_pattern("(?:.*?/)?v?([\\d.]+)\\.tar\\.gz");
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?([\\d.]+)\\.tar\\.gz".into())
    );

    // Verify URL is preserved
    assert_eq!(entry.url(), "https://github.com/example/tags");

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "https://github.com/example/tags (?:.*?/)?v?([\\d.]+)\\.tar\\.gz\n"
    );
}

#[test]
fn test_set_matching_pattern_with_all_fields() {
    // Test with all fields present
    let wf: super::WatchFile = r#"version=4
opts=compression=xz https://example.com/releases (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );

    entry.set_matching_pattern(".*/version-([\\d.]+)\\.tar\\.xz");
    assert_eq!(
        entry.matching_pattern(),
        Some(".*/version-([\\d.]+)\\.tar\\.xz".into())
    );

    // Verify all other fields are preserved
    assert_eq!(entry.url(), "https://example.com/releases");
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Debian)));
    assert_eq!(entry.script(), Some("uupdate".into()));
    assert_eq!(entry.compression(), Ok(Some(super::Compression::Xz)));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=compression=xz https://example.com/releases .*/version-([\\d.]+)\\.tar\\.xz debian uupdate\n"
    );
}

#[test]
fn test_set_version_policy() {
    // Test setting version policy
    let wf: super::WatchFile = r#"version=4
https://example.com/releases (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Debian)));

    entry.set_version_policy("previous");
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Previous)));

    // Verify all other fields are preserved
    assert_eq!(entry.url(), "https://example.com/releases");
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );
    assert_eq!(entry.script(), Some("uupdate".into()));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "https://example.com/releases (?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz previous uupdate\n"
    );
}

#[test]
fn test_set_version_policy_with_options() {
    // Test with options and continuation
    let wf: super::WatchFile = r#"version=4
opts=repack,compression=xz \
    https://github.com/example/example-cat/tags \
        (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Debian)));

    entry.set_version_policy("ignore");
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Ignore)));

    // Verify all other fields are preserved
    assert_eq!(entry.url(), "https://github.com/example/example-cat/tags");
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );
    assert_eq!(entry.script(), Some("uupdate".into()));
    assert!(entry.repack());

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        r#"opts=repack,compression=xz \
    https://github.com/example/example-cat/tags \
        (?:.*?/)?v?(\d[\d.]*)\.tar\.gz ignore uupdate
"#
    );
}

#[test]
fn test_set_script() {
    // Test setting script
    let wf: super::WatchFile = r#"version=4
https://example.com/releases (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.script(), Some("uupdate".into()));

    entry.set_script("uscan");
    assert_eq!(entry.script(), Some("uscan".into()));

    // Verify all other fields are preserved
    assert_eq!(entry.url(), "https://example.com/releases");
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Debian)));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "https://example.com/releases (?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz debian uscan\n"
    );
}

#[test]
fn test_set_script_with_options() {
    // Test with options
    let wf: super::WatchFile = r#"version=4
opts=compression=xz https://example.com/releases (?:.*?/)?v?(\d[\d.]*)\.tar\.gz debian uupdate
"#
    .parse()
    .unwrap();

    let mut entry = wf.entries().next().unwrap();
    assert_eq!(entry.script(), Some("uupdate".into()));

    entry.set_script("custom-script.sh");
    assert_eq!(entry.script(), Some("custom-script.sh".into()));

    // Verify all other fields are preserved
    assert_eq!(entry.url(), "https://example.com/releases");
    assert_eq!(
        entry.matching_pattern(),
        Some("(?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz".into())
    );
    assert_eq!(entry.version(), Ok(Some(super::VersionPolicy::Debian)));
    assert_eq!(entry.compression(), Ok(Some(super::Compression::Xz)));

    // Verify the exact serialized output
    assert_eq!(
        entry.to_string(),
        "opts=compression=xz https://example.com/releases (?:.*?/)?v?(\\d[\\d.]*)\\.tar\\.gz debian custom-script.sh\n"
    );
}

#[test]
fn test_apply_dversionmangle() {
    // Test basic dversionmangle
    let wf: super::WatchFile = r#"version=4
opts=dversionmangle=s/\+dfsg$// https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_dversionmangle("1.0+dfsg").unwrap(), "1.0");
    assert_eq!(entry.apply_dversionmangle("1.0").unwrap(), "1.0");

    // Test with versionmangle (fallback)
    let wf: super::WatchFile = r#"version=4
opts=versionmangle=s/^v// https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_dversionmangle("v1.0").unwrap(), "1.0");

    // Test with both dversionmangle and versionmangle (dversionmangle takes precedence)
    let wf: super::WatchFile = r#"version=4
opts=dversionmangle=s/\+ds//,versionmangle=s/^v// https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_dversionmangle("1.0+ds").unwrap(), "1.0");

    // Test without any mangle options
    let wf: super::WatchFile = r#"version=4
https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_dversionmangle("1.0+dfsg").unwrap(), "1.0+dfsg");
}

#[test]
fn test_apply_oversionmangle() {
    // Test basic oversionmangle - adding suffix
    let wf: super::WatchFile = r#"version=4
opts=oversionmangle=s/$/-1/ https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_oversionmangle("1.0").unwrap(), "1.0-1");
    assert_eq!(entry.apply_oversionmangle("2.5.3").unwrap(), "2.5.3-1");

    // Test oversionmangle for adding +dfsg suffix
    let wf: super::WatchFile = r#"version=4
opts=oversionmangle=s/$/.dfsg/ https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_oversionmangle("1.0").unwrap(), "1.0.dfsg");

    // Test without any mangle options
    let wf: super::WatchFile = r#"version=4
https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_oversionmangle("1.0").unwrap(), "1.0");
}

#[test]
fn test_apply_dirversionmangle() {
    // Test basic dirversionmangle - removing 'v' prefix
    let wf: super::WatchFile = r#"version=4
opts=dirversionmangle=s/^v// https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_dirversionmangle("v1.0").unwrap(), "1.0");
    assert_eq!(entry.apply_dirversionmangle("v2.5.3").unwrap(), "2.5.3");

    // Test dirversionmangle with capture groups
    let wf: super::WatchFile = r#"version=4
opts=dirversionmangle=s/v(\d)/$1/ https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_dirversionmangle("v1.0").unwrap(), "1.0");

    // Test without any mangle options
    let wf: super::WatchFile = r#"version=4
https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_dirversionmangle("v1.0").unwrap(), "v1.0");
}

#[test]
fn test_apply_filenamemangle() {
    // Test filenamemangle to generate tarball filename
    let wf: super::WatchFile = r#"version=4
opts=filenamemangle=s/.+\/v?(\d\S+)\.tar\.gz/mypackage-$1.tar.gz/ https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(
        entry
            .apply_filenamemangle("https://example.com/v1.0.tar.gz")
            .unwrap(),
        "mypackage-1.0.tar.gz"
    );
    assert_eq!(
        entry
            .apply_filenamemangle("https://example.com/2.5.3.tar.gz")
            .unwrap(),
        "mypackage-2.5.3.tar.gz"
    );

    // Test filenamemangle with different pattern
    let wf: super::WatchFile = r#"version=4
opts=filenamemangle=s/.*\/(.*)/$1/ https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(
        entry
            .apply_filenamemangle("https://example.com/path/to/file.tar.gz")
            .unwrap(),
        "file.tar.gz"
    );

    // Test without any mangle options
    let wf: super::WatchFile = r#"version=4
https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(
        entry
            .apply_filenamemangle("https://example.com/file.tar.gz")
            .unwrap(),
        "https://example.com/file.tar.gz"
    );
}

#[test]
fn test_apply_pagemangle() {
    // Test pagemangle to decode HTML entities
    let wf: super::WatchFile = r#"version=4
opts=pagemangle=s/&amp;/&/g https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(
        entry.apply_pagemangle(b"foo &amp; bar").unwrap(),
        b"foo & bar"
    );
    assert_eq!(
        entry
            .apply_pagemangle(b"&amp; foo &amp; bar &amp;")
            .unwrap(),
        b"& foo & bar &"
    );

    // Test pagemangle with different pattern
    let wf: super::WatchFile = r#"version=4
opts=pagemangle=s/<[^>]+>//g https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(entry.apply_pagemangle(b"<div>text</div>").unwrap(), b"text");

    // Test without any mangle options
    let wf: super::WatchFile = r#"version=4
https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(
        entry.apply_pagemangle(b"foo &amp; bar").unwrap(),
        b"foo &amp; bar"
    );
}

#[test]
fn test_apply_downloadurlmangle() {
    // Test downloadurlmangle to change URL path
    let wf: super::WatchFile = r#"version=4
opts=downloadurlmangle=s|/archive/|/download/| https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(
        entry
            .apply_downloadurlmangle("https://example.com/archive/file.tar.gz")
            .unwrap(),
        "https://example.com/download/file.tar.gz"
    );

    // Test downloadurlmangle with different pattern
    let wf: super::WatchFile = r#"version=4
opts=downloadurlmangle=s/github\.com/raw.githubusercontent.com/ https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(
        entry
            .apply_downloadurlmangle("https://github.com/user/repo/file.tar.gz")
            .unwrap(),
        "https://raw.githubusercontent.com/user/repo/file.tar.gz"
    );

    // Test without any mangle options
    let wf: super::WatchFile = r#"version=4
https://example.com/ .*
"#
    .parse()
    .unwrap();
    let entry = wf.entries().next().unwrap();
    assert_eq!(
        entry
            .apply_downloadurlmangle("https://example.com/archive/file.tar.gz")
            .unwrap(),
        "https://example.com/archive/file.tar.gz"
    );
}
