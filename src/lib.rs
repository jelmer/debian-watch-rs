//! Parser and editor for Debian watch files
//!
//! # Example
//!
//! ```rust
//! ```

mod lex;
mod parse;

pub const DEFAULT_VERSION: u32 = 1;

#[cfg(test)]
pub static WATCHV1: &str = r#"version=4
opts=filenamemangle=s/.+\/v?(\d\S+)\.tar\.gz/syncthing-gtk-$1\.tar\.gz/ \
  https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
"#;

#[cfg(test)]
pub static WATCHV2: &str = r#"version=4
https://github.com/syncthing/syncthing-gtk/tags .*/v?(\d\S+)\.tar\.gz
# comment
"#;

/// Let's start with defining all kinds of tokens and
/// composite nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(non_camel_case_types)]
#[repr(u16)]
pub(crate) enum SyntaxKind {
    KEY = 0,
    VALUE,
    EQUALS,
    COMMA,
    CONTINUATION,
    NEWLINE,
    WHITESPACE, // whitespaces is explicit
    COMMENT,    // comments
    ERROR,      // as well as errors

    // composite nodes
    ROOT,      // The entire file
    VERSION,   // "version=x\n"
    ENTRY,     // "opts=foo=blah https://foo.com/bar .*/v?(\d\S+)\.tar\.gz\n"
    OPTS_LIST, // "opts=foo=blah"
    OPTION,    // "foo=blah"
}

/// Convert our `SyntaxKind` into the rowan `SyntaxKind`.
impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}
