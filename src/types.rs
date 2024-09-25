use std::str::FromStr;

/// The type of the component
pub enum ComponentType {
    /// Perl component
    Perl,

    /// NodeJS component
    NodeJS,
}

impl std::fmt::Display for ComponentType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ComponentType::Perl => "perl",
                ComponentType::NodeJS => "nodejs",
            }
        )
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
/// Compression type
pub enum Compression {
    /// Gzip compression
    Gzip,

    /// Xz compression
    Xz,

    /// Bzip2 compression
    Bzip2,

    /// Lzma compression
    Lzma,

    #[default]
    /// Default compression
    Default,
}

impl std::fmt::Display for Compression {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Compression::Gzip => "gzip",
                Compression::Xz => "xz",
                Compression::Bzip2 => "bzip2",
                Compression::Lzma => "lzma",
                Compression::Default => "default",
            }
        )
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
/// How to generate upstream version string from git tags
pub enum Pretty {
    /// Use git describe to generate the version string
    Describe,

    /// Use a custom pattern to generate the version string
    Pattern(String),
}

impl Default for Pretty {
    fn default() -> Self {
        Pretty::Pattern("0.0~git%cd.h%".to_string())
    }
}

impl std::fmt::Display for Pretty {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Pretty::Describe => "describe",
                Pretty::Pattern(pattern) => pattern,
            }
        )
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
/// Git export mode
pub enum GitExport {
    #[default]
    /// Export only files in the .orig.tar archive that are not ignored by the upstream.
    Default,

    /// Export all files in the .orig.tar archive, ignoring any export-ignore git attributes
    /// defined by the upstream.
    All,
}

impl std::fmt::Display for GitExport {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                GitExport::Default => "default".to_string(),
                GitExport::All => "all".to_string(),
            }
        )
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
/// Git clone operation mode
pub enum GitMode {
    #[default]
    /// Clone the git repository in shallow mode
    Shallow,

    /// Clone the git repository in full mode
    Full,
}

impl std::fmt::Display for GitMode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                GitMode::Shallow => "shallow".to_string(),
                GitMode::Full => "full".to_string(),
            }
        )
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
/// PGP verification mode
pub enum PgpMode {
    /// check possible URLs for the signature file and autogenerate a ``pgpsigurlmangle`` rule to
    /// use it
    Auto,

    #[default]
    /// Use pgpsigurlmangle=rules to generate the candidate upstream signature file URL string from
    /// the upstream tarball URL.
    ///
    /// If the specified pgpsigurlmangle is missing, uscan checks possible URLs for the signature
    /// file and suggests adding a pgpsigurlmangle rule.
    ///
    Default,

    /// Use pgpsigurlmangle=rules to generate the candidate upstream signature file URL string from the upstream tarball URL.
    Mangle,

    /// Verify this downloaded tarball file with the signature file specified in the next watch
    /// line. The next watch line must be pgpmode=previous. Otherwise, no verification occurs.
    Next,

    /// Verify the downloaded tarball file specified in the previous watch line with this signature
    /// file.  The previous watch line must be pgpmode=next.
    Previous,

    /// Verify the downloaded file foo.ext with its self signature and extract its content tarball
    /// file as foo.
    SelfSignature,

    /// Verify tag signature if mode=git.
    GitTag,
}

impl std::fmt::Display for PgpMode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                PgpMode::Auto => "auto",
                PgpMode::Default => "default",
                PgpMode::Mangle => "mangle",
                PgpMode::Next => "next",
                PgpMode::Previous => "previous",
                PgpMode::SelfSignature => "self",
                PgpMode::GitTag => "gittag",
            }
        )
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
/// How to search for the upstream tarball
pub enum SearchMode {
    #[default]
    /// Search for the upstream tarball in the HTML page
    Html,

    /// Search for the upstream tarball in the plain text page
    Plain,
}

impl std::fmt::Display for SearchMode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                SearchMode::Html => "html",
                SearchMode::Plain => "plain",
            }
        )
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
/// Archive download mode
pub enum Mode {
    #[default]
    /// downloads the specified tarball from the archive URL on the web. Automatically internal
    /// mode value is updated to either http or ftp by URL.
    LWP,

    /// Access  the  upstream git archive directly with the git command and packs the source tree
    /// with the specified tag via matching-pattern into spkg-version.tar.xz.
    Git,

    /// Access the upstream Subversion archive directly with the svn command and packs the source
    /// tree.
    Svn,
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Mode::LWP => "lwp",
                Mode::Git => "git",
                Mode::Svn => "svn",
            }
        )
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
/// The version policy to use when downloading upstream tarballs
pub enum VersionPolicy {
    #[default]
    /// Requires the downloading upstream tarball to be newer than the version obtained from debian/changelog
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

impl std::fmt::Display for VersionPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            VersionPolicy::Debian => write!(f, "debian"),
            VersionPolicy::Version(v) => write!(f, "version-{}", v),
            VersionPolicy::Same => write!(f, "same"),
            VersionPolicy::Previous => write!(f, "previous"),
            VersionPolicy::Ignore => write!(f, "ignore"),
            VersionPolicy::Group => write!(f, "group"),
            VersionPolicy::Checksum => write!(f, "checksum"),
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
