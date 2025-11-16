use deb822_lossless::{Deb822, Paragraph};
use std::str::FromStr;

use crate::types::ParseError;

/// A watch file in format 5 (RFC822/deb822 style)
#[derive(Debug)]
pub struct WatchFileV5(Deb822);

/// An entry in a format 5 watch file
pub struct EntryV5 {
    paragraph: Paragraph,
}

impl WatchFileV5 {
    /// Create a new empty format 5 watch file
    pub fn new() -> Self {
        // Create a minimal format 5 watch file from a string
        let content = "Version: 5\n";
        WatchFileV5::from_str(content).expect("Failed to create empty watch file")
    }

    /// Returns the version of the watch file (always 5 for this type)
    pub fn version(&self) -> u32 {
        5
    }

    /// Returns an iterator over all entries in the watch file.
    /// The first paragraph contains defaults, subsequent paragraphs are entries.
    pub fn entries(&self) -> impl Iterator<Item = EntryV5> + '_ {
        let paragraphs: Vec<_> = self.0.paragraphs().collect();

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
            .map(|p| EntryV5 { paragraph: p })
    }

    /// Get the underlying Deb822 object
    pub fn inner(&self) -> &Deb822 {
        &self.0
    }
}

impl Default for WatchFileV5 {
    fn default() -> Self {
        Self::new()
    }
}

impl FromStr for WatchFileV5 {
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
                    return Err(ParseError {
                        type_name: "WatchFileV5",
                        value: format!("Expected version 5, got {}", version),
                    });
                }

                Ok(WatchFileV5(deb822))
            }
            Err(e) => Err(ParseError {
                type_name: "WatchFileV5",
                value: e.to_string(),
            }),
        }
    }
}

impl std::fmt::Display for WatchFileV5 {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl EntryV5 {
    /// Get a field value from the entry
    /// TODO: Support defaults from the first paragraph
    pub(crate) fn get_field(&self, key: &str) -> Option<String> {
        // Try the key as-is first
        if let Some(value) = self.paragraph.get(key) {
            return Some(value);
        }

        // If not found, try with different case variations
        // deb822-lossless is case-preserving, so we need to check all field names
        let normalized_key = normalize_key(key);

        // Iterate through all keys in the paragraph and check for normalized match
        for (k, v) in self.paragraph.items() {
            if normalize_key(&k) == normalized_key {
                return Some(v);
            }
        }

        None
    }

    /// Returns the source URL
    pub fn source(&self) -> Option<String> {
        self.get_field("Source")
    }

    /// Returns the matching pattern
    pub fn matching_pattern_v5(&self) -> Option<String> {
        self.get_field("Matching-Pattern")
    }

    /// Get the underlying paragraph
    pub fn paragraph(&self) -> &Paragraph {
        &self.paragraph
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
    use crate::traits::WatchEntry;

    #[test]
    fn test_create_v5_watchfile() {
        let wf = WatchFileV5::new();
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

        let wf: WatchFileV5 = input.parse().unwrap();
        assert_eq!(wf.version(), 5);

        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        let entry = &entries[0];
        assert_eq!(entry.url(), "https://github.com/owner/repo/tags");
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

        let wf: WatchFileV5 = input.parse().unwrap();
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 2);

        assert_eq!(entries[0].url(), "https://github.com/owner/repo1/tags");
        assert_eq!(entries[1].url(), "https://github.com/owner/repo2/tags");
    }

    #[test]
    fn test_v5_case_insensitive_fields() {
        let input = r#"Version: 5

source: https://example.com/files
matching-pattern: .*\.tar\.gz
"#;

        let wf: WatchFileV5 = input.parse().unwrap();
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        let entry = &entries[0];
        assert_eq!(entry.url(), "https://example.com/files");
        assert_eq!(entry.matching_pattern(), Some(".*\\.tar\\.gz".to_string()));
    }

    #[test]
    fn test_v5_with_compression_option() {
        let input = r#"Version: 5

Source: https://example.com/files
Matching-Pattern: .*\.tar\.gz
Compression: xz
"#;

        let wf: WatchFileV5 = input.parse().unwrap();
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        let entry = &entries[0];
        let compression = entry.compression().unwrap();
        assert!(compression.is_some());
    }

    #[test]
    fn test_v5_with_component() {
        let input = r#"Version: 5

Source: https://example.com/files
Matching-Pattern: .*\.tar\.gz
Component: foo
"#;

        let wf: WatchFileV5 = input.parse().unwrap();
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

        let result: Result<WatchFileV5, _> = input.parse();
        assert!(result.is_err());
    }

    #[test]
    fn test_v5_trait_implementation() {
        let input = r#"Version: 5

Source: https://example.com/files
Matching-Pattern: .*\.tar\.gz
"#;

        let wf: WatchFileV5 = input.parse().unwrap();

        // Test WatchFileFormat trait
        assert_eq!(wf.version(), 5);
        let entries: Vec<_> = wf.entries().collect();
        assert_eq!(entries.len(), 1);

        // Test WatchEntry trait
        let entry = &entries[0];
        assert_eq!(entry.url(), "https://example.com/files");
        assert!(entry.matching_pattern().is_some());
    }

    #[test]
    fn test_v5_roundtrip() {
        let input = r#"Version: 5

Source: https://example.com/files
Matching-Pattern: .*\.tar\.gz
"#;

        let wf: WatchFileV5 = input.parse().unwrap();
        let output = wf.to_string();

        // The output should be parseable again
        let wf2: WatchFileV5 = output.parse().unwrap();
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
}
