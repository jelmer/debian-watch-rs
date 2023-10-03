use std::str::FromStr;

pub enum ComponentType {
    Perl,
    NodeJS,
}

impl ToString for ComponentType {
    fn to_string(&self) -> String {
        match self {
            ComponentType::Perl => "perl".to_string(),
            ComponentType::NodeJS => "nodejs".to_string(),
        }
    }
}

impl FromStr for ComponentType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "perl" => Ok(ComponentType::Perl),
            "nodejs" => Ok(ComponentType::NodeJS),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Compression {
    Gzip,
    Xz,
    Bzip2,
    Lzma,
    #[default]
    Default,
}

impl ToString for Compression {
    fn to_string(&self) -> String {
        match self {
            Compression::Gzip => "gzip".to_string(),
            Compression::Xz => "xz".to_string(),
            Compression::Bzip2 => "bzip2".to_string(),
            Compression::Lzma => "lzma".to_string(),
            Compression::Default => "default".to_string(),
        }
    }
}

impl FromStr for Compression {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "gz" | "gzip" => Ok(Compression::Gzip),
            "xz" => Ok(Compression::Xz),
            "bz2" | "bzip2" => Ok(Compression::Bzip2),
            "lzma" => Ok(Compression::Lzma),
            "default" => Ok(Compression::Default),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pretty {
    Describe,
    Pattern(String),
}

impl Default for Pretty {
    fn default() -> Self {
        Pretty::Pattern("0.0~git%cd.h%".to_string())
    }
}

impl ToString for Pretty {
    fn to_string(&self) -> String {
        match self {
            Pretty::Describe => "describe".to_string(),
            Pretty::Pattern(pattern) => pattern.clone(),
        }
    }
}

impl FromStr for Pretty {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "describe" {
            Ok(Pretty::Describe)
        } else {
            Ok(Pretty::Pattern(s.to_string()))
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum GitExport {
    #[default]
    Default,
    All,
}

impl ToString for GitExport {
    fn to_string(&self) -> String {
        match self {
            GitExport::Default => "default".to_string(),
            GitExport::All => "all".to_string(),
        }
    }
}

impl FromStr for GitExport {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "default" => Ok(GitExport::Default),
            "all" => Ok(GitExport::All),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum GitMode {
    #[default]
    Shallow,
    Full,
}

impl ToString for GitMode {
    fn to_string(&self) -> String {
        match self {
            GitMode::Shallow => "shallow".to_string(),
            GitMode::Full => "full".to_string(),
        }
    }
}

impl FromStr for GitMode {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "shallow" => Ok(GitMode::Shallow),
            "full" => Ok(GitMode::Full),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum PgpMode {
    Auto,
    #[default]
    Default,
    Mangle,
    Next,
    Previous,
    SelfSignature,
    GitTag,
}

impl ToString for PgpMode {
    fn to_string(&self) -> String {
        match self {
            PgpMode::Auto => "auto".to_string(),
            PgpMode::Default => "default".to_string(),
            PgpMode::Mangle => "mangle".to_string(),
            PgpMode::Next => "next".to_string(),
            PgpMode::Previous => "previous".to_string(),
            PgpMode::SelfSignature => "self".to_string(),
            PgpMode::GitTag => "gittag".to_string(),
        }
    }
}

impl FromStr for PgpMode {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "auto" => Ok(PgpMode::Auto),
            "default" => Ok(PgpMode::Default),
            "mangle" => Ok(PgpMode::Mangle),
            "next" => Ok(PgpMode::Next),
            "previous" => Ok(PgpMode::Previous),
            "self" => Ok(PgpMode::SelfSignature),
            "gittag" => Ok(PgpMode::GitTag),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SearchMode {
    #[default]
    Html,
    Plain,
}

impl ToString for SearchMode {
    fn to_string(&self) -> String {
        match self {
            SearchMode::Html => "html".to_string(),
            SearchMode::Plain => "plain".to_string(),
        }
    }
}

impl FromStr for SearchMode {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "html" => Ok(SearchMode::Html),
            "plain" => Ok(SearchMode::Plain),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Mode {
    #[default]
    LWP,
    Git,
    Svn,
}

impl ToString for Mode {
    fn to_string(&self) -> String {
        match self {
            Mode::LWP => "lwp".to_string(),
            Mode::Git => "git".to_string(),
            Mode::Svn => "svn".to_string(),
        }
    }
}

impl FromStr for Mode {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "lwp" => Ok(Mode::LWP),
            "git" => Ok(Mode::Git),
            "svn" => Ok(Mode::Svn),
            _ => Err(()),
        }
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

impl std::str::FromStr for VersionPolicy {
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
