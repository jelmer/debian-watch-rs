//! Functions for searching web pages for upstream releases.

use regex::Regex;
use std::io::Read;

#[cfg(feature = "discover")]
/// Search for version matches in HTML content
///
/// Parses the HTML and searches for links matching the given pattern.
/// Returns an iterator of (version, url) tuples.
///
/// # Arguments
///
/// * `body` - The HTML content to search
/// * `matching_pattern` - Regex pattern to match against URLs
/// * `base_url` - Base URL for resolving relative links
///
/// # Examples
///
/// ```ignore
/// use debian_watch::search::html_search;
///
/// let html = b"<a href='project-1.0.tar.gz'>Download</a>";
/// let results: Vec<_> = html_search(html, r"project-(\d+\.\d+)\.tar\.gz", "https://example.com/")
///     .collect();
/// assert_eq!(results.len(), 1);
/// assert_eq!(results[0].0, "1.0");
/// ```
#[cfg(feature = "discover")]
pub fn html_search(
    body: &[u8],
    matching_pattern: &str,
    base_url: &str,
) -> Box<dyn Iterator<Item = (String, String)>> {
    let html = String::from_utf8_lossy(body);
    let doc = scraper::Html::parse_document(&html);
    let selector = scraper::Selector::parse("a").unwrap();

    let pattern = if matching_pattern.contains('/') {
        matching_pattern.to_string()
    } else {
        // If pattern doesn't contain '/', join it with base_url
        let base = base_url.trim_end_matches('/');
        format!("{}/{}", base, matching_pattern)
    };

    let re = match Regex::new(&pattern) {
        Ok(r) => r,
        Err(_) => return Box::new(std::iter::empty()),
    };

    let base_url = base_url.to_string();
    let results: Vec<(String, String)> = doc
        .select(&selector)
        .filter_map(move |element| {
            let href = element.value().attr("href")?;
            // Resolve relative URLs
            let full_url = if href.starts_with("http://") || href.starts_with("https://") {
                href.to_string()
            } else {
                let base = base_url.trim_end_matches('/');
                if href.starts_with('/') {
                    // Parse base URL to get scheme and host
                    if let Ok(base_parsed) = url::Url::parse(&base_url) {
                        format!(
                            "{}://{}{}",
                            base_parsed.scheme(),
                            base_parsed.host_str().unwrap_or(""),
                            href
                        )
                    } else {
                        format!("{}{}", base, href)
                    }
                } else {
                    format!("{}/{}", base, href)
                }
            };

            // Try to match the pattern
            if let Some(captures) = re.captures(&full_url) {
                // Extract the first capture group as the version
                if let Some(version_match) = captures.get(1) {
                    let version = version_match.as_str().to_string();
                    // Use capture group 0 (full match) as the URL
                    let url = captures.get(0).unwrap().as_str().to_string();
                    Some((version, url))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    Box::new(results.into_iter())
}

/// Search for version matches in plain text content
///
/// Searches the plain text for matches of the given pattern.
/// Returns an iterator of (version, url) tuples.
///
/// # Arguments
///
/// * `body` - The plain text content to search
/// * `matching_pattern` - Regex pattern to match
/// * `base_url` - Base URL for resolving relative links
///
/// # Examples
///
/// ```
/// use debian_watch::search::plain_search;
///
/// let text = b"project-1.0.tar.gz\nproject-2.0.tar.gz";
/// let results: Vec<_> = plain_search(text, r"project-(\d+\.\d+)\.tar\.gz", "https://example.com/")
///     .collect();
/// assert!(results.len() >= 1);
/// ```
pub fn plain_search(
    body: &[u8],
    matching_pattern: &str,
    base_url: &str,
) -> Box<dyn Iterator<Item = (String, String)>> {
    let re = match Regex::new(matching_pattern) {
        Ok(r) => r,
        Err(_) => return Box::new(std::iter::empty()),
    };

    let text = String::from_utf8_lossy(body);
    let base_url = base_url.to_string();

    let results: Vec<(String, String)> = re
        .captures_iter(&text)
        .filter_map(|captures| {
            // Extract the first capture group as the version
            if let Some(version_match) = captures.get(1) {
                let version = version_match.as_str().to_string();
                // Use capture group 0 (full match) for constructing the URL
                let matched = captures.get(0).unwrap().as_str();

                // Resolve to full URL
                let url = if matched.starts_with("http://") || matched.starts_with("https://") {
                    matched.to_string()
                } else {
                    let base = base_url.trim_end_matches('/');
                    format!("{}/{}", base, matched.trim_start_matches('/'))
                };

                Some((version, url))
            } else {
                None
            }
        })
        .collect();

    Box::new(results.into_iter())
}

/// Search for version matches in content
///
/// Dispatches to either html_search or plain_search based on search mode.
pub fn search<R: Read>(
    searchmode: &str,
    mut resp: R,
    matching_pattern: &str,
    _package: &str,
    url: &str,
) -> Result<Box<dyn Iterator<Item = (String, String)>>, std::io::Error> {
    let mut body = Vec::new();
    resp.read_to_end(&mut body)?;

    let iter: Box<dyn Iterator<Item = (String, String)>> = match searchmode {
        #[cfg(feature = "discover")]
        "html" => html_search(&body, matching_pattern, url),
        "plain" => plain_search(&body, matching_pattern, url),
        _ => Box::new(std::iter::empty()),
    };

    Ok(iter)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg(feature = "discover")]
    fn test_html_search() {
        let html = b"<html><body><a href='project-1.0.tar.gz'>v1.0</a><a href='project-2.0.tar.gz'>v2.0</a></body></html>";
        let results: Vec<_> =
            html_search(html, r"project-(\d+\.\d+)\.tar\.gz", "https://example.com/").collect();

        assert_eq!(results.len(), 2);
        assert!(results.iter().any(|(v, _)| v == "1.0"));
        assert!(results.iter().any(|(v, _)| v == "2.0"));
    }

    #[test]
    fn test_plain_search() {
        let text = b"Available: project-1.0.tar.gz project-2.0.tar.gz";
        let results: Vec<_> =
            plain_search(text, r"project-(\d+\.\d+)\.tar\.gz", "https://example.com/").collect();

        assert_eq!(results.len(), 2);
        assert!(results.iter().any(|(v, _)| v == "1.0"));
        assert!(results.iter().any(|(v, _)| v == "2.0"));
    }
}
