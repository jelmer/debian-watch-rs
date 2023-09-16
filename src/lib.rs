mod lex;

/// Let's start with defining all kinds of tokens and
/// composite nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(non_camel_case_types)]
#[repr(u16)]
enum SyntaxKind {
    KEY = 0,
    VALUE,
    EQUALS,
    CONTINUATION,
    NEWLINE,
    WHITESPACE, // whitespaces is explicit
    ERROR,      // as well as errors

    // composite nodes
    VERSION,     // "version=x\n"
    WATCH_ENTRY, // "opts=foo=blah https://foo.com/bar .*/v?(\d\S+)\.tar\.gz\n"
    OPTS_LIST,   // "opts=foo=blah"
}
