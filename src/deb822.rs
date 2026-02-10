//! Watch file implementation for format 5 (RFC822/deb822 style)
use crate::traits::{WatchEntry, WatchFileFormat};
use crate::types::ParseError as TypesParseError;
use crate::VersionPolicy;
use deb822_lossless::{Deb822, Paragraph};
use std::str::FromStr;

#[derive(Debug)]
/// Parse error for watch file parsing
pub struct ParseError(String);

impl std::error::Error for ParseError {}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "ParseError: {}", self.0)
    }
}

/// A watch file in format 5 (RFC822/deb822 style)
#[derive(Debug)]
pub struct WatchFile(Deb822);

/// An entry in a format 5 watch file
pub struct Entry {
    paragraph: Paragraph,
    defaults: Option<Paragraph>,
}

impl WatchFile {
    /// Create a new empty format 5 watch file
    pub fn new() -> Self {
        // Create a minimal format 5 watch file from a string
        let content = "Version: 5\n";
        WatchFile::from_str(content).expect("Failed to create empty watch file")
    }

    /// Returns the version of the watch file (always 5 for this type)
    pub fn version(&self) -> u32 {
        5
    }

    /// Returns the defaults paragraph if it exists.
    /// The defaults paragraph is the second paragraph (after Version) if it has no Source field.
    pub fn defaults(&self) -> Option<Paragraph> {
        let paragraphs: Vec<_> = self.0.paragraphs().collect();

        if paragraphs.len() > 1 {
            // Check if second paragraph looks like defaults (no Source field)
            if !paragraphs[1].contains_key("Source") && !paragraphs[1].contains_key("source") {
                return Some(paragraphs[1].clone());
            }
        }

        None
    }

    /// Returns an iterator over all entries in the watch file.
    /// The first paragraph contains defaults, subsequent paragraphs are entries.
    pub fn entries(&self) -> impl Iterator<Item = Entry> + '_ {
        let paragraphs: Vec<_> = self.0.paragraphs().collect();
        let defaults = self.defaults();

        // Skip the first paragraph (version)
        // The second paragraph (if it exists and has specific fields) contains defaults
        // Otherwise all paragraphs are entries
        let start_index = if paragraphs.len() > 1 {
            // Check if second paragraph looks like defaults (no Source field)
            if !paragraphs[1].contains_key("Source") && !paragraphs[1].contains_key("source") {
                2 // Skip version and defaults
            } else {
                1 // Skip only version
            }
        } else {
            1
        };

        paragraphs
            .into_iter()
            .skip(start_index)
            .map(move |p| Entry {
                paragraph: p,
                defaults: defaults.clone(),
            })
    }

    /// Get the underlying Deb822 object
    pub fn inner(&self) -> &Deb822 {
        &self.0
    }
}

impl Default for WatchFile {
    fn default() -> Self {
        Self::new()
    }
}

impl FromStr for WatchFile {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match Deb822::from_str(s) {
            Ok(deb822) => {
                // Verify it's version 5
                let version = deb822
                    .paragraphs()
                    .next()
                    .and_then(|p| p.get("Version"))
                    .unwrap_or_else(|| "1".to_string());

                if version != "5" {
                    return Err(ParseError(format!("Expected version 5, got {}", version)));
                }

                Ok(WatchFile(deb822))
            }
            Err(e) => Err(ParseError(e.to_string())),
        }
    }
}

impl std::fmt::Display for WatchFile {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Entry {
    /// Get a field value from the entry, with fallback to defaults paragraph.
    /// First checks the entry's own fields, then falls back to the defaults paragraph if present.
    pub(crate) fn get_field(&self, key: &str) -> Option<String> {
        // Try the key as-is first in the entry
        if let Some(value) = self.paragraph.get(key) {
            return Some(value);
        }

        // If not found, try with different case variations in the entry
        // deb822-lossless is case-preserving, so we need to check all field names
        let normalized_key = normalize_key(key);

        // Iterate through all keys in the paragraph and check for normalized match
        for (k, v) in self.paragraph.items() {
            if normalize_key(&k) == normalized_key {
                return Some(v);
            }
        }

        // If not found in entry, check the defaults paragraph
        if let Some(ref defaults) = self.defaults {
            // Try the key as-is first in defaults
            if let Some(value) = defaults.get(key) {
                return Some(value);
            }

            // Try with case variations in defaults
            for (k, v) in defaults.items() {
                if normalize_key(&k) == normalized_key {
                    return Some(v);
                }
            }
        }

        None
    }

    /// Returns the source URL
    pub fn source(&self) -> Option<String> {
        self.get_field("Source")
    }

    /// Returns the matching pattern
    pub fn matching_pattern(&self) -> Option<String> {
        self.get_field("Matching-Pattern")
    }

    /// Get the underlying paragraph
    pub fn as_deb822(&self) -> &Paragraph {
        &self.paragraph
    }

    /// Name of the component, if specified
    pub fn component(&self) -> Option<String> {
        self.get_field("Component")
    }

    /// Get the an option value from the entry, with fallback to defaults paragraph.
    pub fn get_option(&self, key: &str) -> Option<String> {
        match key {
            "Source" => None,           // Source is not an option
            "Matching-Pattern" => None, // Matching-Pattern is not an option
            "Component" => None,        // Component is not an option
            "Version" => None,          // Version is not an option
            key => self.get_field(key),
        }
    }

    /// Set an option value in the entry
    pub fn set_option(&mut self, key: &str, value: &str) {
        self.paragraph.insert(key, value);
    }

    /// Delete an option from the entry
    pub fn delete_option(&mut self, key: &str) {
        self.paragraph.remove(key);
    }
}

/// Normalize a field key according to RFC822 rules:
/// - Convert to lowercase
/// - Hyphens and underscores are treated as equivalent
fn normalize_key(key: &str) -> String {
    key.to_lowercase().replace(['-', '_'], "")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_v5_watchfile() {
        let wf = WatchFile::new();
        assert_eq!(wf.version(), 5);

        let output = wf.to_string();
        assert!(output.contains("Version"));
        assert!(output.contains("5"));
    }

    #[test]
    fn test_parse_v5_basic() {
        let input = r#"Version: 5

Source: https://github.com/owner/repo/tags
Matching-Pattern: .*/v?(\d\S+)\.tar\.gz
"#;

        let wf: WatchFile = input.parse().unwrap();
        assert_eq!(wf.version(), 5);

        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        let entry = &entries[0];
        assert_eq!(
            entry.source().as_deref(),
            Some("https://github.com/owner/repo/tags")
        );
        assert_eq!(
            entry.matching_pattern(),
            Some(".*/v?(\\d\\S+)\\.tar\\.gz".to_string())
        );
    }

    #[test]
    fn test_parse_v5_multiple_entries() {
        let input = r#"Version: 5

Source: https://github.com/owner/repo1/tags
Matching-Pattern: .*/v?(\d\S+)\.tar\.gz

Source: https://github.com/owner/repo2/tags
Matching-Pattern: .*/release-(\d\S+)\.tar\.gz
"#;

        let wf: WatchFile = input.parse().unwrap();
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 2);

        assert_eq!(
            entries[0].source().as_deref(),
            Some("https://github.com/owner/repo1/tags")
        );
        assert_eq!(
            entries[1].source().as_deref(),
            Some("https://github.com/owner/repo2/tags")
        );
    }

    #[test]
    fn test_v5_case_insensitive_fields() {
        let input = r#"Version: 5

source: https://example.com/files
matching-pattern: .*\.tar\.gz
"#;

        let wf: WatchFile = input.parse().unwrap();
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        let entry = &entries[0];
        assert_eq!(entry.source().as_deref(), Some("https://example.com/files"));
        assert_eq!(entry.matching_pattern().as_deref(), Some(".*\\.tar\\.gz"));
    }

    #[test]
    fn test_v5_with_compression_option() {
        let input = r#"Version: 5

Source: https://example.com/files
Matching-Pattern: .*\.tar\.gz
Compression: xz
"#;

        let wf: WatchFile = input.parse().unwrap();
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        let entry = &entries[0];
        let compression = entry.get_option("compression");
        assert!(compression.is_some());
    }

    #[test]
    fn test_v5_with_component() {
        let input = r#"Version: 5

Source: https://example.com/files
Matching-Pattern: .*\.tar\.gz
Component: foo
"#;

        let wf: WatchFile = input.parse().unwrap();
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        let entry = &entries[0];
        assert_eq!(entry.component(), Some("foo".to_string()));
    }

    #[test]
    fn test_v5_rejects_wrong_version() {
        let input = r#"Version: 4

Source: https://example.com/files
Matching-Pattern: .*\.tar\.gz
"#;

        let result: Result<WatchFile, _> = input.parse();
        assert!(result.is_err());
    }

    #[test]
    fn test_v5_roundtrip() {
        let input = r#"Version: 5

Source: https://example.com/files
Matching-Pattern: .*\.tar\.gz
"#;

        let wf: WatchFile = input.parse().unwrap();
        let output = wf.to_string();

        // The output should be parseable again
        let wf2: WatchFile = output.parse().unwrap();
        assert_eq!(wf2.version(), 5);

        let entries: Vec<_> = wf2.entries().collect();
        assert_eq!(entries.len(), 1);
    }

    #[test]
    fn test_normalize_key() {
        assert_eq!(normalize_key("Matching-Pattern"), "matchingpattern");
        assert_eq!(normalize_key("matching_pattern"), "matchingpattern");
        assert_eq!(normalize_key("MatchingPattern"), "matchingpattern");
        assert_eq!(normalize_key("MATCHING-PATTERN"), "matchingpattern");
    }

    #[test]
    fn test_defaults_paragraph() {
        let input = r#"Version: 5

Compression: xz
User-Agent: Custom/1.0

Source: https://example.com/repo1
Matching-Pattern: .*\.tar\.gz

Source: https://example.com/repo2
Matching-Pattern: .*\.tar\.gz
Compression: gz
"#;

        let wf: WatchFile = input.parse().unwrap();

        // Check that defaults paragraph is detected
        let defaults = wf.defaults();
        assert!(defaults.is_some());
        let defaults = defaults.unwrap();
        assert_eq!(defaults.get("Compression"), Some("xz".to_string()));
        assert_eq!(defaults.get("User-Agent"), Some("Custom/1.0".to_string()));

        // Check that entries inherit from defaults
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 2);

        // First entry should inherit Compression and User-Agent from defaults
        assert_eq!(entries[0].get_option("Compression"), Some("xz".to_string()));
        assert_eq!(
            entries[0].get_option("User-Agent"),
            Some("Custom/1.0".to_string())
        );

        // Second entry overrides Compression but inherits User-Agent
        assert_eq!(entries[1].get_option("Compression"), Some("gz".to_string()));
        assert_eq!(
            entries[1].get_option("User-Agent"),
            Some("Custom/1.0".to_string())
        );
    }

    #[test]
    fn test_no_defaults_paragraph() {
        let input = r#"Version: 5

Source: https://example.com/repo1
Matching-Pattern: .*\.tar\.gz
"#;

        let wf: WatchFile = input.parse().unwrap();

        // Check that there's no defaults paragraph (first paragraph has Source)
        assert!(wf.defaults().is_none());

        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);
    }

    #[test]
    fn test_defaults_with_case_variations() {
        let input = r#"Version: 5

compression: xz
user-agent: Custom/1.0

Source: https://example.com/repo1
Matching-Pattern: .*\.tar\.gz
"#;

        let wf: WatchFile = input.parse().unwrap();

        // Check that defaults work with different case
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        // Should find defaults even with different case
        assert_eq!(entries[0].get_option("Compression"), Some("xz".to_string()));
        assert_eq!(
            entries[0].get_option("User-Agent"),
            Some("Custom/1.0".to_string())
        );
    }
}

// Trait implementations for WatchFileFormat and WatchEntry

impl WatchFileFormat for WatchFile {
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

impl WatchEntry for Entry {
    fn url(&self) -> String {
        // In format 5, the URL is in the "Source" field
        self.source().unwrap_or_default()
    }

    fn matching_pattern(&self) -> Option<String> {
        Entry::matching_pattern(self)
    }

    fn version_policy(&self) -> Result<Option<VersionPolicy>, TypesParseError> {
        // Format 5 uses "Version-Policy" field
        match self.get_option("Version-Policy") {
            Some(policy) => Ok(Some(policy.parse()?)),
            None => Ok(None),
        }
    }

    fn script(&self) -> Option<String> {
        // Format 5 uses "Script" field
        self.get_option("Script")
    }

    fn get_option(&self, key: &str) -> Option<String> {
        // Use the internal get_field method which handles normalization
        self.get_field(key)
    }

    fn has_option(&self, key: &str) -> bool {
        self.get_option(key).is_some()
    }
}
