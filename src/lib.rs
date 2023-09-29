//! Formatting-preserving parser and editor for Debian watch files
//!
//! # Example
//!
//! ```rust
//! let wf = debian_watch::WatchFile::new(None);
//! assert_eq!(wf.version(), debian_watch::DEFAULT_VERSION);
//! assert_eq!("", wf.to_string());
//!
//! let wf = debian_watch::WatchFile::new(Some(4));
//! assert_eq!(wf.version(), 4);
//! assert_eq!("version=4\n", wf.to_string());
//!
//! let wf: debian_watch::WatchFile = r#"version=4
//! opts=foo=blah https://foo.com/bar .*/v?(\d\S+)\.tar\.gz
//! "#.parse().unwrap();
//! assert_eq!(wf.version(), 4);
//! assert_eq!(wf.entries().collect::<Vec<_>>().len(), 1);
//! let entry = wf.entries().next().unwrap();
//! assert_eq!(entry.opts(), maplit::hashmap! {
//!    "foo".to_string() => "blah".to_string(),
//! });
//! assert_eq!(&entry.url(), "https://foo.com/bar");
//! assert_eq!(entry.matching_pattern().as_deref(), Some(".*/v?(\\d\\S+)\\.tar\\.gz"));
//! ```

mod lex;
mod parse;
use std::str::FromStr;

/// Any watch files without a version are assumed to be
/// version 1.
pub const DEFAULT_VERSION: u32 = 1;

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

pub use crate::parse::Entry;
pub use crate::parse::WatchFile;

#[cfg(test)]
mod tests {
    #[test]
    fn test_create_watchfile() {
        let wf = super::WatchFile::new(None);
        assert_eq!(wf.version(), super::DEFAULT_VERSION);

        assert_eq!("", wf.to_string());

        let wf = super::WatchFile::new(Some(4));
        assert_eq!(wf.version(), 4);

        assert_eq!("version=4\n", wf.to_string());
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum VersionPolicy {
    #[default]
    // Requires the downloading upstream tarball to be newer than the version obtained from debian/changelog
    Debian,

    /// Requires the upstream tarball to be newer than specified version
    Version(debversion::Version),

    /// Requires the downloaded version of the secondary tarballs to be exactly the same as the one for the first upstream tarball downloaded
    Same,

    /// Restricts the version of the seignature file (used with pgpmode=previous)
    Previous,

    /// Does not restrict the version of the secondary tarballs
    Ignore,

    /// Requires the downloading upstream tarball to be newer than the version obtained from
    /// debian/changelog. Package version is the concatenation of all "group" upstream version.
    Group,

    /// Requires the downloading upstream tarball to be newer than the version obtained from
    /// debian/changelog. Package version is the concatenation of the version of the main tarball,
    /// followed by a checksum of all the tarballs using the checksum version system. At least the
    /// main upstream source has to be declared as group.
    Checksum,
}

impl ToString for VersionPolicy {
    fn to_string(&self) -> String {
        match self {
            VersionPolicy::Debian => "debian".to_string(),
            VersionPolicy::Version(v) => format!("version-{}", v.to_string()),
            VersionPolicy::Same => "same".to_string(),
            VersionPolicy::Previous => "previous".to_string(),
            VersionPolicy::Ignore => "ignore".to_string(),
            VersionPolicy::Group => "group".to_string(),
            VersionPolicy::Checksum => "checksum".to_string(),
        }
    }
}

impl FromStr for VersionPolicy {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "debian" => Ok(VersionPolicy::Debian),
            "same" => Ok(VersionPolicy::Same),
            "previous" => Ok(VersionPolicy::Previous),
            "ignore" => Ok(VersionPolicy::Ignore),
            "group" => Ok(VersionPolicy::Group),
            "checksum" => Ok(VersionPolicy::Checksum),
            s if s.starts_with("version-") => {
                let v = s.trim_start_matches("version-");
                Ok(VersionPolicy::Version(
                    v.parse::<debversion::Version>()
                        .map_err(|e| e.to_string())?,
                ))
            }
            _ => Err(format!("Unknown version policy: {}", s)),
        }
    }
}

#[cfg(test)]
mod version_policy_tests {
    use super::VersionPolicy;
    use std::str::FromStr;

    #[test]
    fn test_version_policy_to_string() {
        assert_eq!("debian", VersionPolicy::Debian.to_string());
        assert_eq!("same", VersionPolicy::Same.to_string());
        assert_eq!("previous", VersionPolicy::Previous.to_string());
        assert_eq!("ignore", VersionPolicy::Ignore.to_string());
        assert_eq!("group", VersionPolicy::Group.to_string());
        assert_eq!("checksum", VersionPolicy::Checksum.to_string());
        assert_eq!(
            "version-1.2.3",
            VersionPolicy::Version("1.2.3".parse().unwrap()).to_string()
        );
    }

    #[test]
    fn test_version_policy_from_str() {
        assert_eq!(
            VersionPolicy::Debian,
            VersionPolicy::from_str("debian").unwrap()
        );
        assert_eq!(
            VersionPolicy::Same,
            VersionPolicy::from_str("same").unwrap()
        );
        assert_eq!(
            VersionPolicy::Previous,
            VersionPolicy::from_str("previous").unwrap()
        );
        assert_eq!(
            VersionPolicy::Ignore,
            VersionPolicy::from_str("ignore").unwrap()
        );
        assert_eq!(
            VersionPolicy::Group,
            VersionPolicy::from_str("group").unwrap()
        );
        assert_eq!(
            VersionPolicy::Checksum,
            VersionPolicy::from_str("checksum").unwrap()
        );
        assert_eq!(
            VersionPolicy::Version("1.2.3".parse().unwrap()),
            VersionPolicy::from_str("version-1.2.3").unwrap()
        );
    }
}
