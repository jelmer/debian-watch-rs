//! Conversion between watch file formats

use crate::parse::{Entry, WatchFile};
use crate::parse_v5::WatchFileV5;
use crate::SyntaxKind::*;
use deb822_lossless::{Deb822, Paragraph};

/// Error type for conversion failures
#[derive(Debug)]
pub enum ConversionError {
    /// Unknown option that cannot be converted to v5 field name
    UnknownOption(String),
    /// Invalid version policy value
    InvalidVersionPolicy(String),
}

impl std::fmt::Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ConversionError::UnknownOption(opt) => {
                write!(f, "Unknown option '{}' cannot be converted to v5", opt)
            }
            ConversionError::InvalidVersionPolicy(err) => {
                write!(f, "Invalid version policy: {}", err)
            }
        }
    }
}

impl std::error::Error for ConversionError {}

/// Convert a watch file from formats 1-4 to format 5
///
/// This function preserves comments from the original file by inserting them
/// into the CST of the generated v5 watch file.
pub fn convert_to_v5(watch_file: &WatchFile) -> Result<WatchFileV5, ConversionError> {
    // Create a Deb822 with version header as first paragraph
    let mut paragraphs = vec![vec![("Version", "5")].into_iter().collect()];

    // Extract leading comments (before any entries)
    let leading_comments = extract_leading_comments(watch_file);

    // Convert each entry to a paragraph
    for _entry in watch_file.entries() {
        let para: deb822_lossless::Paragraph =
            vec![("Source", "placeholder")].into_iter().collect();
        paragraphs.push(para);
    }

    let deb822: Deb822 = paragraphs.into_iter().collect();

    // Now populate the entry paragraphs
    let mut para_iter = deb822.paragraphs();
    para_iter.next(); // Skip version paragraph

    for (entry, mut para) in watch_file.entries().zip(para_iter) {
        // Extract and insert comments associated with this entry
        let entry_comments = extract_entry_comments(&entry);
        for comment in entry_comments {
            para.insert_comment_before(&comment);
        }

        // Convert entry to v5 format
        convert_entry_to_v5(&entry, &mut para)?;
    }

    // Insert leading comments before the first entry paragraph if any
    if !leading_comments.is_empty() {
        if let Some(mut first_entry_para) = deb822.paragraphs().nth(1) {
            for comment in leading_comments.iter().rev() {
                first_entry_para.insert_comment_before(comment);
            }
        }
    }

    // Convert to WatchFileV5
    let output = deb822.to_string();
    output
        .parse()
        .map_err(|_| ConversionError::UnknownOption("Failed to parse generated v5".to_string()))
}

/// Extract leading comments from the watch file (before any entries)
fn extract_leading_comments(watch_file: &WatchFile) -> Vec<String> {
    let mut comments = Vec::new();
    let syntax = watch_file.syntax();

    for child in syntax.children_with_tokens() {
        match child {
            rowan::NodeOrToken::Token(token) => {
                if token.kind() == COMMENT {
                    // Extract comment text without the leading '# ' since
                    // insert_comment_before() will add "# {comment}"
                    let text = token.text();
                    let comment = text
                        .strip_prefix("# ")
                        .or_else(|| text.strip_prefix('#'))
                        .unwrap_or(text);
                    comments.push(comment.to_string());
                }
            }
            rowan::NodeOrToken::Node(node) => {
                // Stop when we hit an entry
                if node.kind() == ENTRY {
                    break;
                }
            }
        }
    }

    comments
}

/// Extract comments associated with an entry
fn extract_entry_comments(entry: &Entry) -> Vec<String> {
    let mut comments = Vec::new();
    let syntax = entry.syntax();

    // Get comments that appear before or within this entry
    for child in syntax.children_with_tokens() {
        if let rowan::NodeOrToken::Token(token) = child {
            if token.kind() == COMMENT {
                // Extract comment text without the leading '# ' since
                // insert_comment_before() will add "# {comment}"
                let text = token.text();
                let comment = text
                    .strip_prefix("# ")
                    .or_else(|| text.strip_prefix('#'))
                    .unwrap_or(text);
                comments.push(comment.to_string());
            }
        }
    }

    comments
}

/// Convert a single entry from v1-v4 format to v5 format
fn convert_entry_to_v5(entry: &Entry, para: &mut Paragraph) -> Result<(), ConversionError> {
    // Source field (URL)
    let url = entry.url();
    if !url.is_empty() {
        para.set("Source", &url);
    }

    // Matching-Pattern field
    if let Some(pattern) = entry.matching_pattern() {
        para.set("Matching-Pattern", &pattern);
    }

    // Version policy
    match entry.version() {
        Ok(Some(version_policy)) => {
            para.set("Version-Policy", &version_policy.to_string());
        }
        Err(err) => return Err(ConversionError::InvalidVersionPolicy(err)),
        Ok(None) => {}
    }

    // Script
    if let Some(script) = entry.script() {
        para.set("Script", &script);
    }

    // Convert all options to fields
    if let Some(opts_list) = entry.option_list() {
        for (key, value) in opts_list.options() {
            // Convert option names to Title-Case with hyphens
            let field_name = option_to_field_name(&key)?;
            para.set(&field_name, &value);
        }
    }

    Ok(())
}

/// Convert option names from v1-v4 format to v5 field names
///
/// Returns an error for unknown options instead of using heuristics.
///
/// Examples:
/// - "filenamemangle" -> "Filename-Mangle"
/// - "mode" -> "Mode"
/// - "pgpmode" -> "PGP-Mode"
fn option_to_field_name(option: &str) -> Result<String, ConversionError> {
    // Special cases for known options
    match option {
        "mode" => Ok("Mode".to_string()),
        "component" => Ok("Component".to_string()),
        "ctype" => Ok("Component-Type".to_string()),
        "compression" => Ok("Compression".to_string()),
        "repack" => Ok("Repack".to_string()),
        "repacksuffix" => Ok("Repack-Suffix".to_string()),
        "bare" => Ok("Bare".to_string()),
        "user-agent" => Ok("User-Agent".to_string()),
        "pasv" | "passive" => Ok("Passive".to_string()),
        "active" | "nopasv" => Ok("Active".to_string()),
        "unzipopt" => Ok("Unzip-Options".to_string()),
        "decompress" => Ok("Decompress".to_string()),
        "dversionmangle" => Ok("Debian-Version-Mangle".to_string()),
        "uversionmangle" => Ok("Upstream-Version-Mangle".to_string()),
        "downloadurlmangle" => Ok("Download-URL-Mangle".to_string()),
        "filenamemangle" => Ok("Filename-Mangle".to_string()),
        "pgpsigurlmangle" => Ok("PGP-Signature-URL-Mangle".to_string()),
        "oversionmangle" => Ok("Original-Version-Mangle".to_string()),
        "pagemangle" => Ok("Page-Mangle".to_string()),
        "dirversionmangle" => Ok("Directory-Version-Mangle".to_string()),
        "versionmangle" => Ok("Version-Mangle".to_string()),
        "hrefdecode" => Ok("Href-Decode".to_string()),
        "pgpmode" => Ok("PGP-Mode".to_string()),
        "gitmode" => Ok("Git-Mode".to_string()),
        "gitexport" => Ok("Git-Export".to_string()),
        "pretty" => Ok("Pretty".to_string()),
        "date" => Ok("Date".to_string()),
        "searchmode" => Ok("Search-Mode".to_string()),
        // Return error for unknown options
        _ => Err(ConversionError::UnknownOption(option.to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::traits::WatchEntry;

    #[test]
    fn test_simple_conversion() {
        let v4_input = r#"version=4
https://example.com/files .*/v?(\d+\.\d+)\.tar\.gz
"#;

        let v4_file: WatchFile = v4_input.parse().unwrap();
        let v5_file = convert_to_v5(&v4_file).unwrap();

        assert_eq!(v5_file.version(), 5);

        let entries: Vec<_> = v5_file.entries().collect();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].url(), "https://example.com/files");
        assert_eq!(
            entries[0].matching_pattern(),
            Some(".*/v?(\\d+\\.\\d+)\\.tar\\.gz".to_string())
        );
    }

    #[test]
    fn test_conversion_with_options() {
        let v4_input = r#"version=4
opts=filenamemangle=s/.*\/(.*)/$1/,compression=xz https://example.com/files .*/v?(\d+)\.tar\.gz
"#;

        let v4_file: WatchFile = v4_input.parse().unwrap();
        let v5_file = convert_to_v5(&v4_file).unwrap();

        let entries: Vec<_> = v5_file.entries().collect();
        assert_eq!(entries.len(), 1);

        let entry = &entries[0];
        assert_eq!(
            entry.get_option("Filename-Mangle"),
            Some("s/.*\\/(.*)/$1/".to_string())
        );
        assert_eq!(entry.get_option("Compression"), Some("xz".to_string()));
    }

    #[test]
    fn test_conversion_with_comments() {
        // Use a simpler case for now - comment at the beginning before version
        let v4_input = r#"# This is a comment about the package
version=4
opts=filenamemangle=s/.*\/(.*)/$1/ https://example.com/files .*/v?(\d+)\.tar\.gz
"#;

        let v4_file: WatchFile = v4_input.parse().unwrap();
        let v5_file = convert_to_v5(&v4_file).unwrap();

        let output = ToString::to_string(&v5_file);

        // Check that comment is preserved
        assert!(output.contains("# This is a comment about the package"));
        assert!(output.contains("Version: 5"));
    }

    #[test]
    fn test_conversion_multiple_entries() {
        let v4_input = r#"version=4
https://example.com/repo1 .*/v?(\d+)\.tar\.gz
https://example.com/repo2 .*/release-(\d+)\.tar\.gz
"#;

        let v4_file: WatchFile = v4_input.parse().unwrap();
        let v5_file = convert_to_v5(&v4_file).unwrap();

        let entries: Vec<_> = v5_file.entries().collect();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].url(), "https://example.com/repo1");
        assert_eq!(entries[1].url(), "https://example.com/repo2");
    }

    #[test]
    fn test_option_to_field_name() {
        assert_eq!(option_to_field_name("mode").unwrap(), "Mode");
        assert_eq!(
            option_to_field_name("filenamemangle").unwrap(),
            "Filename-Mangle"
        );
        assert_eq!(option_to_field_name("pgpmode").unwrap(), "PGP-Mode");
        assert_eq!(option_to_field_name("user-agent").unwrap(), "User-Agent");
        assert_eq!(option_to_field_name("compression").unwrap(), "Compression");
    }

    #[test]
    fn test_option_to_field_name_unknown() {
        let result = option_to_field_name("unknownoption");
        assert!(result.is_err());
        match result {
            Err(ConversionError::UnknownOption(opt)) => {
                assert_eq!(opt, "unknownoption");
            }
            _ => panic!("Expected UnknownOption error"),
        }
    }

    #[test]
    fn test_roundtrip_conversion() {
        let v4_input = r#"version=4
opts=compression=xz,component=foo https://example.com/files .*/(\d+)\.tar\.gz
"#;

        let v4_file: WatchFile = v4_input.parse().unwrap();
        let v5_file = convert_to_v5(&v4_file).unwrap();

        // Verify the v5 file can be parsed back
        let v5_str = ToString::to_string(&v5_file);
        let v5_reparsed: WatchFileV5 = v5_str.parse().unwrap();

        let entries: Vec<_> = v5_reparsed.entries().collect();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].component(), Some("foo".to_string()));
    }
}
