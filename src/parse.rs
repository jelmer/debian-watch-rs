use crate::lex::lex;
use crate::types::*;
use crate::SyntaxKind;
use crate::SyntaxKind::*;
use crate::DEFAULT_VERSION;
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

/// The parse results are stored as a "green tree".
/// We'll discuss working with the results later
struct Parse {
    green_node: GreenNode,
    #[allow(unused)]
    errors: Vec<String>,
}

fn parse(text: &str) -> Parse {
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
        fn parse_version(&mut self) -> Option<i32> {
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
                } else {
                    let version_str = self.tokens.last().unwrap().1.clone();
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
            for i in 1..3 {
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
                    self.bump();
                    self.builder.finish_node();
                } else {
                    self.bump();
                }
                self.skip_ws();
            }
            if self.current() != Some(NEWLINE) {
                self.builder.start_node(ERROR.into());
                self.errors
                    .push(format!("expected newline, not {:?}", self.current()));
                self.bump();
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
                self.bump();
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
                    self.bump();
                    self.builder.finish_node();
                } else {
                    self.bump();
                }
                loop {
                    if !self.parse_option() {
                        break;
                    }
                    if self.current() == Some(COMMA) {
                        self.bump();
                    } else {
                        break;
                    }
                }
                self.builder.finish_node();
                self.skip_ws();
            }
        }

        fn parse(mut self) -> Parse {
            let mut version = 1;
            // Make sure that the root node covers all source
            self.builder.start_node(ROOT.into());
            if let Some(v) = self.parse_version() {
                version = v;
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
            Parse {
                green_node: self.builder.finish(),
                errors: self.errors,
            }
        }
        /// Advance one token, adding it to the current branch of the tree builder.
        fn bump(&mut self) {
            let (kind, text) = self.tokens.pop().unwrap();
            self.builder.token(kind.into(), text.as_str());
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

impl Parse {
    fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green_node.clone())
    }

    fn root(&self) -> WatchFile {
        WatchFile::cast(self.syntax()).unwrap()
    }
}

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(PartialEq, Eq, Hash)]
        #[repr(transparent)]
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

        impl ToString for $ast {
            fn to_string(&self) -> String {
                self.0.text().to_string()
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

impl Version {
    /// Returns the version of the watch file.
    pub fn version(&self) -> u32 {
        self.0
            .children_with_tokens()
            .find_map(|it| match it {
                SyntaxElement::Token(token) => {
                    if token.kind() == VALUE {
                        Some(token.text().parse().unwrap())
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
    pub fn option_list(&self) -> Option<OptionList> {
        self.0.children().find_map(OptionList::cast)
    }

    pub fn get_option(&self, key: &str) -> Option<String> {
        self.option_list().and_then(|ol| ol.get_option(key))
    }

    pub fn has_option(&self, key: &str) -> bool {
        self.option_list().map_or(false, |ol| ol.has_option(key))
    }

    /// The name of the secondary source tarball
    pub fn component(&self) -> Option<String> {
        self.get_option("component")
    }

    pub fn ctype(&self) -> Option<ComponentType> {
        self.get_option("ctype").and_then(|it| it.parse().ok())
    }

    pub fn compression(&self) -> Option<Compression> {
        self.get_option("compression")
            .and_then(|it| it.parse().ok())
    }

    pub fn repack(&self) -> bool {
        self.has_option("repack")
    }

    pub fn repacksuffix(&self) -> Option<String> {
        self.get_option("repacksuffix")
    }

    pub fn mode(&self) -> Option<Mode> {
        self.get_option("mode").and_then(|it| it.parse().ok())
    }

    pub fn pretty(&self) -> Pretty {
        self.get_option("pretty")
            .and_then(|it| it.parse().ok())
            .unwrap_or_default()
    }

    pub fn date(&self) -> String {
        self.get_option("date")
            .unwrap_or_else(|| "%Y%m%d".to_string())
    }

    pub fn gitexport(&self) -> GitExport {
        self.get_option("gitexport")
            .and_then(|it| it.parse().ok())
            .unwrap_or_default()
    }

    pub fn gitmode(&self) -> GitMode {
        self.get_option("gitmode")
            .and_then(|it| it.parse().ok())
            .unwrap_or_default()
    }

    pub fn pgpmode(&self) -> PgpMode {
        self.get_option("pgpmode")
            .and_then(|it| it.parse().ok())
            .unwrap_or_default()
    }

    pub fn searchmode(&self) -> SearchMode {
        self.get_option("searchmode")
            .and_then(|it| it.parse().ok())
            .unwrap_or_default()
    }

    pub fn decompress(&self) -> bool {
        self.has_option("decompress")
    }

    pub fn bare(&self) -> bool {
        self.has_option("bare")
    }

    pub fn user_agent(&self) -> Option<String> {
        self.get_option("user-agent")
    }

    pub fn passive(&self) -> Option<bool> {
        if self.has_option("passive") || self.has_option("pasv") {
            Some(true)
        } else if self.has_option("active") || self.has_option("nopasv") {
            Some(false)
        } else {
            None
        }
    }

    pub fn unzipoptions(&self) -> Option<String> {
        self.get_option("unzipopt")
    }

    pub fn dversionmangle(&self) -> Option<String> {
        self.get_option("dversionmangle")
    }

    pub fn dirversionmangle(&self) -> Option<String> {
        self.get_option("dirversionmangle")
    }

    pub fn pagemangle(&self) -> Option<String> {
        self.get_option("pagemangle")
    }

    pub fn uversionmangle(&self) -> Option<String> {
        self.get_option("uversionmangle")
    }

    pub fn versionmangle(&self) -> Option<String> {
        self.get_option("versionmangle")
    }

    pub fn hrefdecode(&self) -> bool {
        self.get_option("hrefdecode").is_some()
    }

    pub fn downloadurlmangle(&self) -> Option<String> {
        self.get_option("downloadurlmangle")
    }

    pub fn filenamemangle(&self) -> Option<String> {
        self.get_option("filenamemangle")
    }

    pub fn pgpsigurlmangle(&self) -> Option<String> {
        self.get_option("pgpsigurlmangle")
    }

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
        self.items().next().unwrap()
    }

    /// Returns the matching pattern of the entry.
    pub fn matching_pattern(&self) -> Option<String> {
        self.items().nth(1)
    }

    /// Returns the version policy
    pub fn version(&self) -> Option<crate::VersionPolicy> {
        self.items().nth(2).and_then(|it| it.parse().ok())
    }

    /// Returns the script of the entry.
    pub fn script(&self) -> Option<String> {
        self.items().nth(3)
    }

    /// Replace all substitutions and return the resulting URL.
    pub fn format_url(&self, package: impl FnOnce() -> String) -> url::Url {
        subst(self.url().as_str(), package).parse().unwrap()
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
    let mut substs = SUBSTITUTIONS.to_vec();
    let package_name;
    if text.contains("@PACKAGE@") {
        package_name = Some(package());
        substs.push(("@PACKAGE@", package_name.as_deref().unwrap()));
    }

    let mut text = text.to_string();

    for (k, v) in substs {
        text = text.replace(k, v);
    }

    text
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
        for child in self.children() {
            if child.key().as_deref() == Some(key) {
                return child.value();
            }
        }
        None
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
    assert_eq!(entry.version(), None);
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
