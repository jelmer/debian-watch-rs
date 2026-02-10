//! Format detection and parsing for watch files

/// Error type for parsing watch files
#[derive(Debug)]
pub enum ParseError {
    /// Error parsing line-based format (v1-4)
    #[cfg(feature = "linebased")]
    LineBased(crate::linebased::ParseError),
    /// Error parsing deb822 format (v5)
    #[cfg(feature = "deb822")]
    Deb822(crate::deb822::ParseError),
    /// Could not detect version
    UnknownVersion,
    /// Feature not enabled
    FeatureNotEnabled(String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            #[cfg(feature = "linebased")]
            ParseError::LineBased(e) => write!(f, "{}", e),
            #[cfg(feature = "deb822")]
            ParseError::Deb822(e) => write!(f, "{}", e),
            ParseError::UnknownVersion => write!(f, "Could not detect watch file version"),
            ParseError::FeatureNotEnabled(msg) => write!(f, "{}", msg),
        }
    }
}

impl std::error::Error for ParseError {}

/// Detected watch file format
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WatchFileVersion {
    /// Line-based format (versions 1-4)
    LineBased(u32),
    /// Deb822 format (version 5)
    Deb822,
}

/// Detect the version/format of a watch file from its content
///
/// This function examines the content to determine if it's a line-based
/// format (v1-4) or deb822 format (v5).
///
/// After detecting the version, you can either:
/// - Use the `parse()` function to automatically parse and return a `ParsedWatchFile`
/// - Parse directly: `content.parse::<debian_watch::linebased::WatchFile>()`
///
/// # Examples
///
/// ```
/// use debian_watch::parse::{detect_version, WatchFileVersion};
///
/// let v4_content = "version=4\nhttps://example.com/ .*.tar.gz";
/// assert_eq!(detect_version(v4_content), Some(WatchFileVersion::LineBased(4)));
///
/// let v5_content = "Version: 5\n\nSource: https://example.com/";
/// assert_eq!(detect_version(v5_content), Some(WatchFileVersion::Deb822));
/// ```
pub fn detect_version(content: &str) -> Option<WatchFileVersion> {
    let trimmed = content.trim_start();

    // Check if it starts with RFC822-style "Version: 5"
    if trimmed.starts_with("Version:") || trimmed.starts_with("version:") {
        // Try to extract the version number
        if let Some(first_line) = trimmed.lines().next() {
            if let Some(colon_pos) = first_line.find(':') {
                let version_str = first_line[colon_pos + 1..].trim();
                if version_str == "5" {
                    return Some(WatchFileVersion::Deb822);
                }
            }
        }
    }

    // Otherwise, it's line-based format
    // Try to detect the version from "version=N" line
    for line in trimmed.lines() {
        let line = line.trim();

        // Skip comments and blank lines
        if line.starts_with('#') || line.is_empty() {
            continue;
        }

        // Check for version=N
        if line.starts_with("version=") || line.starts_with("version =") {
            let version_part = if line.starts_with("version=") {
                &line[8..]
            } else {
                &line[9..]
            };

            if let Ok(version) = version_part.trim().parse::<u32>() {
                return Some(WatchFileVersion::LineBased(version));
            }
        }

        // If we hit a non-comment, non-version line, assume default version
        break;
    }

    // Default to version 1 for line-based format
    Some(WatchFileVersion::LineBased(crate::DEFAULT_VERSION))
}

/// Parsed watch file that can be either line-based or deb822 format
#[derive(Debug)]
pub enum ParsedWatchFile {
    /// Line-based watch file (v1-4)
    #[cfg(feature = "linebased")]
    LineBased(crate::linebased::WatchFile),
    /// Deb822 watch file (v5)
    #[cfg(feature = "deb822")]
    Deb822(crate::deb822::WatchFile),
}

/// Parsed watch entry that can be either line-based or deb822 format
#[derive(Debug)]
pub enum ParsedEntry {
    /// Line-based entry (v1-4)
    #[cfg(feature = "linebased")]
    LineBased(crate::linebased::Entry),
    /// Deb822 entry (v5)
    #[cfg(feature = "deb822")]
    Deb822(crate::deb822::Entry),
}

impl ParsedWatchFile {
    /// Get the version of the watch file
    pub fn version(&self) -> u32 {
        match self {
            #[cfg(feature = "linebased")]
            ParsedWatchFile::LineBased(wf) => wf.version(),
            #[cfg(feature = "deb822")]
            ParsedWatchFile::Deb822(wf) => wf.version(),
        }
    }

    /// Get an iterator over entries as ParsedEntry enum
    pub fn entries(&self) -> impl Iterator<Item = ParsedEntry> + '_ {
        // We need to collect because we can't return different iterator types from match arms
        let entries: Vec<_> = match self {
            #[cfg(feature = "linebased")]
            ParsedWatchFile::LineBased(wf) => wf.entries().map(ParsedEntry::LineBased).collect(),
            #[cfg(feature = "deb822")]
            ParsedWatchFile::Deb822(wf) => wf.entries().map(ParsedEntry::Deb822).collect(),
        };
        entries.into_iter()
    }
}

impl ParsedEntry {
    /// Get the URL/Source of the entry
    pub fn url(&self) -> String {
        match self {
            #[cfg(feature = "linebased")]
            ParsedEntry::LineBased(e) => e.url(),
            #[cfg(feature = "deb822")]
            ParsedEntry::Deb822(e) => e.source().unwrap_or_default(),
        }
    }

    /// Get the matching pattern
    pub fn matching_pattern(&self) -> Option<String> {
        match self {
            #[cfg(feature = "linebased")]
            ParsedEntry::LineBased(e) => e.matching_pattern(),
            #[cfg(feature = "deb822")]
            ParsedEntry::Deb822(e) => e.matching_pattern(),
        }
    }

    /// Get a generic option/field value by key (case-insensitive)
    ///
    /// This handles the difference between line-based format (lowercase keys)
    /// and deb822 format (capitalized keys). It tries the key as-is first,
    /// then tries with the first letter capitalized.
    pub fn get_option(&self, key: &str) -> Option<String> {
        match self {
            #[cfg(feature = "linebased")]
            ParsedEntry::LineBased(e) => e.get_option(key),
            #[cfg(feature = "deb822")]
            ParsedEntry::Deb822(e) => {
                // Try exact match first, then try capitalized
                e.get_field(key).or_else(|| {
                    let mut chars = key.chars();
                    if let Some(first) = chars.next() {
                        let capitalized = first.to_uppercase().chain(chars).collect::<String>();
                        e.get_field(&capitalized)
                    } else {
                        None
                    }
                })
            }
        }
    }

    /// Check if an option/field is set (case-insensitive)
    pub fn has_option(&self, key: &str) -> bool {
        self.get_option(key).is_some()
    }

    /// Get the script
    pub fn script(&self) -> Option<String> {
        self.get_option("script")
    }

    /// Format the URL with package substitution
    pub fn format_url(
        &self,
        package: impl FnOnce() -> String,
    ) -> Result<url::Url, url::ParseError> {
        crate::subst::subst(&self.url(), package).parse()
    }

    /// Get the user agent
    pub fn user_agent(&self) -> Option<String> {
        self.get_option("user-agent")
    }

    /// Get the pagemangle option
    pub fn pagemangle(&self) -> Option<String> {
        self.get_option("pagemangle")
    }

    /// Get the uversionmangle option
    pub fn uversionmangle(&self) -> Option<String> {
        self.get_option("uversionmangle")
    }

    /// Get the downloadurlmangle option
    pub fn downloadurlmangle(&self) -> Option<String> {
        self.get_option("downloadurlmangle")
    }

    /// Get the pgpsigurlmangle option
    pub fn pgpsigurlmangle(&self) -> Option<String> {
        self.get_option("pgpsigurlmangle")
    }

    /// Get the filenamemangle option
    pub fn filenamemangle(&self) -> Option<String> {
        self.get_option("filenamemangle")
    }

    /// Get the oversionmangle option
    pub fn oversionmangle(&self) -> Option<String> {
        self.get_option("oversionmangle")
    }

    /// Get the searchmode, with default fallback
    pub fn searchmode(&self) -> crate::types::SearchMode {
        self.get_option("searchmode")
            .and_then(|s| s.parse().ok())
            .unwrap_or_default()
    }
}

impl std::fmt::Display for ParsedWatchFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            #[cfg(feature = "linebased")]
            ParsedWatchFile::LineBased(wf) => write!(f, "{}", wf),
            #[cfg(feature = "deb822")]
            ParsedWatchFile::Deb822(wf) => write!(f, "{}", wf),
        }
    }
}

/// Parse a watch file with automatic format detection
///
/// This function detects whether the input is line-based (v1-4) or
/// deb822 format (v5) and parses it accordingly, returning a unified
/// ParsedWatchFile enum.
///
/// # Examples
///
/// ```
/// # #[cfg(feature = "linebased")]
/// # {
/// use debian_watch::parse::parse;
///
/// let content = "version=4\nhttps://example.com/ .*.tar.gz";
/// let parsed = parse(content).unwrap();
/// assert_eq!(parsed.version(), 4);
/// # }
/// ```
pub fn parse(content: &str) -> Result<ParsedWatchFile, ParseError> {
    let version = detect_version(content).ok_or(ParseError::UnknownVersion)?;

    match version {
        #[cfg(feature = "linebased")]
        WatchFileVersion::LineBased(_v) => {
            let wf: crate::linebased::WatchFile = content.parse().map_err(ParseError::LineBased)?;
            Ok(ParsedWatchFile::LineBased(wf))
        }
        #[cfg(not(feature = "linebased"))]
        WatchFileVersion::LineBased(_v) => Err(ParseError::FeatureNotEnabled(
            "linebased feature required for v1-4 formats".to_string(),
        )),
        #[cfg(feature = "deb822")]
        WatchFileVersion::Deb822 => {
            let wf: crate::deb822::WatchFile = content.parse().map_err(ParseError::Deb822)?;
            Ok(ParsedWatchFile::Deb822(wf))
        }
        #[cfg(not(feature = "deb822"))]
        WatchFileVersion::Deb822 => Err(ParseError::FeatureNotEnabled(
            "deb822 feature required for v5 format".to_string(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_version_v1_default() {
        let content = "https://example.com/ .*.tar.gz";
        assert_eq!(
            detect_version(content),
            Some(WatchFileVersion::LineBased(1))
        );
    }

    #[test]
    fn test_detect_version_v4() {
        let content = "version=4\nhttps://example.com/ .*.tar.gz";
        assert_eq!(
            detect_version(content),
            Some(WatchFileVersion::LineBased(4))
        );
    }

    #[test]
    fn test_detect_version_v4_with_spaces() {
        let content = "version = 4\nhttps://example.com/ .*.tar.gz";
        assert_eq!(
            detect_version(content),
            Some(WatchFileVersion::LineBased(4))
        );
    }

    #[test]
    fn test_detect_version_v5() {
        let content = "Version: 5\n\nSource: https://example.com/";
        assert_eq!(detect_version(content), Some(WatchFileVersion::Deb822));
    }

    #[test]
    fn test_detect_version_v5_lowercase() {
        let content = "version: 5\n\nSource: https://example.com/";
        assert_eq!(detect_version(content), Some(WatchFileVersion::Deb822));
    }

    #[test]
    fn test_detect_version_with_leading_comments() {
        let content = "# This is a comment\nversion=4\nhttps://example.com/ .*.tar.gz";
        assert_eq!(
            detect_version(content),
            Some(WatchFileVersion::LineBased(4))
        );
    }

    #[test]
    fn test_detect_version_with_leading_whitespace() {
        let content = "  \n  version=3\nhttps://example.com/ .*.tar.gz";
        assert_eq!(
            detect_version(content),
            Some(WatchFileVersion::LineBased(3))
        );
    }

    #[test]
    fn test_detect_version_v2() {
        let content = "version=2\nhttps://example.com/ .*.tar.gz";
        assert_eq!(
            detect_version(content),
            Some(WatchFileVersion::LineBased(2))
        );
    }

    #[cfg(feature = "linebased")]
    #[test]
    fn test_parse_linebased() {
        let content = "version=4\nhttps://example.com/ .*.tar.gz";
        let parsed = parse(content).unwrap();
        assert_eq!(parsed.version(), 4);
    }

    #[cfg(feature = "deb822")]
    #[test]
    fn test_parse_deb822() {
        let content = "Version: 5\n\nSource: https://example.com/\nMatching-Pattern: .*.tar.gz";
        let parsed = parse(content).unwrap();
        assert_eq!(parsed.version(), 5);
    }

    #[cfg(all(feature = "linebased", feature = "deb822"))]
    #[test]
    fn test_parse_both_formats() {
        // Test v4
        let v4_content = "version=4\nhttps://example.com/ .*.tar.gz";
        let v4_parsed = parse(v4_content).unwrap();
        assert_eq!(v4_parsed.version(), 4);

        // Test v5
        let v5_content = "Version: 5\n\nSource: https://example.com/\nMatching-Pattern: .*.tar.gz";
        let v5_parsed = parse(v5_content).unwrap();
        assert_eq!(v5_parsed.version(), 5);
    }

    #[cfg(feature = "linebased")]
    #[test]
    fn test_parse_roundtrip() {
        let content = "version=4\n# Comment\nhttps://example.com/ .*.tar.gz";
        let parsed = parse(content).unwrap();
        let output = parsed.to_string();

        // Parse again
        let reparsed = parse(&output).unwrap();
        assert_eq!(reparsed.version(), 4);
    }
}
