use crate::lex::lex;
use crate::SyntaxKind;
use crate::SyntaxKind::*;
use crate::DEFAULT_VERSION;

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
                    self.errors.push("expected value".to_string());
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
                if self.current() != Some(VALUE) {
                    self.builder.start_node(ERROR.into());
                    self.errors.push("expected value".to_string());
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
                self.errors.push("expected value".to_string());
                self.bump();
                self.builder.finish_node();
            } else {
                self.bump();
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

    fn root(&self) -> Root {
        Root::cast(self.syntax()).unwrap()
    }
}

macro_rules! ast_node {
    ($ast:ident, $kind:ident) => {
        #[derive(PartialEq, Eq, Hash)]
        #[repr(transparent)]
        struct $ast(SyntaxNode);
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
    };
}

ast_node!(Root, ROOT);
ast_node!(Version, VERSION);
ast_node!(Entry, ENTRY);
ast_node!(OptionList, OPTS_LIST);
ast_node!(_Option, OPTION);

impl Root {
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
    pub fn options(&self) -> Option<OptionList> {
        self.0.children().find_map(OptionList::cast)
    }

    fn items(&self) -> impl Iterator<Item = String> + '_ {
        self.0.children_with_tokens().filter_map(|it| match it {
            SyntaxElement::Token(token) => {
                if token.kind() == VALUE {
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

    pub fn version(&self) -> Option<String> {
        self.items().nth(2)
    }

    pub fn script(&self) -> Option<String> {
        self.items().nth(3)
    }
}

impl OptionList {
    pub fn options(&self) -> impl Iterator<Item = _Option> + '_ {
        self.0.children().filter_map(_Option::cast)
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
        self.0.children_with_tokens().find_map(|it| match it {
            SyntaxElement::Token(token) => {
                if token.kind() == VALUE {
                    Some(token.text().to_string())
                } else {
                    None
                }
            }
            _ => None,
        })
    }
}

#[test]
fn test_parse_v1() {
    let parsed = parse(crate::WATCHV1);
    assert_eq!(parsed.errors, Vec::<String>::new());
    let node = parsed.syntax();
    assert_eq!(
        format!("{:#?}", node),
        r#"ROOT@0..156
  VERSION@0..10
    KEY@0..7 "version"
    EQUALS@7..8 "="
    VALUE@8..9 "4"
    NEWLINE@9..10 "\n"
  ENTRY@10..156
    OPTS_LIST@10..81
      KEY@10..14 "opts"
      EQUALS@14..15 "="
      OPTION@15..81
        KEY@15..29 "filenamemangle"
        EQUALS@29..30 "="
        VALUE@30..81 "s/.+\\/v?(\\d\\S+)\\.tar\\ ..."
    WHITESPACE@81..82 " "
    CONTINUATION@82..84 "\\\n"
    WHITESPACE@84..86 "  "
    VALUE@86..133 "https://github.com/sy ..."
    WHITESPACE@133..134 " "
    VALUE@134..155 ".*/v?(\\d\\S+)\\.tar\\.gz"
    NEWLINE@155..156 "\n"
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

    assert_eq!(node.text(), crate::WATCHV1);
}

#[test]
fn test_parse_v2() {
    let parsed = parse(crate::WATCHV2);
    assert_eq!(parsed.errors, Vec::<String>::new());
    let node = parsed.syntax();
    println!("{:#?}", node);
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
}
