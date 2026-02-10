//! Discover upstream releases from watch file entries
//!
//! This module provides traits for discovering upstream releases by fetching URLs
//! and searching for version patterns. The traits provide a common interface
//! across all watch file formats.

use crate::release::Release;
use crate::traits::{WatchEntry, WatchFileFormat};
use crate::DEFAULT_USER_AGENT;
use std::error::Error;

/// Error type for discovery operations
#[derive(Debug)]
pub enum DiscoveryError {
    /// HTTP request failed
    HttpError(String),
    /// Pattern matching failed
    PatternError(String),
    /// Missing required field
    MissingField(String),
    /// URL parsing error
    UrlError(String),
    /// IO error
    IoError(String),
}

impl std::fmt::Display for DiscoveryError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            DiscoveryError::HttpError(msg) => write!(f, "HTTP error: {}", msg),
            DiscoveryError::PatternError(msg) => write!(f, "Pattern error: {}", msg),
            DiscoveryError::MissingField(msg) => write!(f, "Missing field: {}", msg),
            DiscoveryError::UrlError(msg) => write!(f, "URL error: {}", msg),
            DiscoveryError::IoError(msg) => write!(f, "IO error: {}", msg),
        }
    }
}

impl Error for DiscoveryError {}

impl From<std::io::Error> for DiscoveryError {
    fn from(err: std::io::Error) -> Self {
        DiscoveryError::IoError(err.to_string())
    }
}

impl From<reqwest::Error> for DiscoveryError {
    fn from(err: reqwest::Error) -> Self {
        DiscoveryError::HttpError(err.to_string())
    }
}

impl From<url::ParseError> for DiscoveryError {
    fn from(err: url::ParseError) -> Self {
        DiscoveryError::UrlError(err.to_string())
    }
}

/// Trait for discovering upstream releases from watch entries
///
/// This trait provides methods for fetching URLs and discovering available
/// releases based on the watch file configuration.
pub trait Discover: WatchEntry {
    /// Discover all available releases for this watch entry (async version)
    ///
    /// Fetches the URL specified in the watch entry and searches for releases
    /// matching the configured pattern.
    ///
    /// # Arguments
    ///
    /// * `package` - Closure that returns the package name to use for substitution in URLs
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use debian_watch::traits::WatchFileFormat;
    /// use debian_watch::discover::Discover;
    ///
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let wf: debian_watch::WatchFile = r#"version=4
    /// https://example.com/files .*/v?(\\d\\S+)\\.tar\\.gz
    /// "#.parse()?;
    ///
    /// let entry = wf.entries().next().unwrap();
    /// let releases = entry.discover(|| "mypackage".to_string()).await?;
    /// for release in releases {
    ///     println!("Found version: {}", release.version);
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn discover(
        &self,
        package: impl FnOnce() -> String + Send,
    ) -> impl std::future::Future<Output = Result<Vec<Release>, DiscoveryError>> + Send
    where
        Self: Sized,
    {
        self.discover_impl(package, None)
    }

    /// Discover all available releases with a custom HTTP client (async version)
    ///
    /// This is the same as `discover()` but allows providing a custom reqwest client
    /// for more control over HTTP requests.
    fn discover_with_client(
        &self,
        package: impl FnOnce() -> String + Send,
        client: &reqwest::Client,
    ) -> impl std::future::Future<Output = Result<Vec<Release>, DiscoveryError>> + Send
    where
        Self: Sized,
    {
        self.discover_impl(package, Some(client))
    }

    /// Internal implementation for discovering releases
    fn discover_impl(
        &self,
        package: impl FnOnce() -> String + Send,
        client: Option<&reqwest::Client>,
    ) -> impl std::future::Future<Output = Result<Vec<Release>, DiscoveryError>> + Send
    where
        Self: Sized,
    {
        // Extract all data from self before async block
        let url_result = self.format_url(package);
        let user_agent = self
            .user_agent()
            .unwrap_or_else(|| DEFAULT_USER_AGENT.to_string());
        let matching_pattern = self.matching_pattern();
        let searchmode_result = self.searchmode();
        let pagemangle = self.pagemangle();
        let uversionmangle = self.uversionmangle();
        let downloadurlmangle = self.downloadurlmangle();
        let pgpsigurlmangle_opt = self.pgpsigurlmangle();
        let filenamemangle_opt = self.filenamemangle();
        let oversionmangle_opt = self.oversionmangle();

        async move {
            let url = url_result.map_err(|e| DiscoveryError::UrlError(e.to_string()))?;

            // Build HTTP client if not provided
            let default_client;
            let http_client = if let Some(c) = client {
                c
            } else {
                default_client = reqwest::Client::builder()
                    .user_agent(user_agent)
                    .build()
                    .map_err(|e| DiscoveryError::HttpError(e.to_string()))?;
                &default_client
            };

            // Fetch the URL
            let response = http_client
                .get(url.as_str())
                .send()
                .await
                .map_err(|e| DiscoveryError::HttpError(e.to_string()))?;

            let body = response
                .bytes()
                .await
                .map_err(|e| DiscoveryError::HttpError(e.to_string()))?;

            // Apply pagemangle if present
            let mangled_body = if let Some(mangle) = pagemangle {
                let page_str = String::from_utf8_lossy(&body);
                let result = crate::mangle::apply_mangle(&mangle, &page_str)
                    .map_err(|e| DiscoveryError::PatternError(e.to_string()))?;
                result.into_bytes()
            } else {
                body.to_vec()
            };

            // Get the matching pattern
            let pattern_str = matching_pattern
                .ok_or_else(|| DiscoveryError::MissingField("matching_pattern".to_string()))?;

            // Apply substitution to the matching pattern
            let package_name = String::new();
            let pattern = crate::subst::subst(&pattern_str, || package_name.clone());

            // Determine search mode
            let searchmode =
                searchmode_result.map_err(|e| DiscoveryError::PatternError(e.to_string()))?;
            let searchmode_str = searchmode.to_string();

            // Search for versions
            let results = crate::search::search(
                &searchmode_str,
                std::io::Cursor::new(mangled_body.as_ref() as &[u8]),
                &pattern,
                &package_name,
                url.as_str(),
            )?;

            // Apply mangles to each result and convert to Release objects
            let mut releases = Vec::new();
            for (version, full_url) in results {
                // Apply uversionmangle
                let mangled_version = if let Some(vm) = &uversionmangle {
                    crate::mangle::apply_mangle(vm, &version)
                        .map_err(|e| DiscoveryError::PatternError(e.to_string()))?
                } else {
                    version
                };

                // Apply downloadurlmangle
                let mangled_url = if let Some(vm) = &downloadurlmangle {
                    crate::mangle::apply_mangle(vm, &full_url)
                        .map_err(|e| DiscoveryError::PatternError(e.to_string()))?
                } else {
                    full_url
                };

                // Apply pgpsigurlmangle if present
                let pgpsigurl = if let Some(mangle) = &pgpsigurlmangle_opt {
                    Some(
                        crate::mangle::apply_mangle(mangle, &mangled_url)
                            .map_err(|e| DiscoveryError::PatternError(e.to_string()))?,
                    )
                } else {
                    None
                };

                // Apply filenamemangle if present
                let target_filename = if let Some(mangle) = &filenamemangle_opt {
                    Some(
                        crate::mangle::apply_mangle(mangle, &mangled_url)
                            .map_err(|e| DiscoveryError::PatternError(e.to_string()))?,
                    )
                } else {
                    None
                };

                // Apply oversionmangle if present
                let package_version = if let Some(vm) = &oversionmangle_opt {
                    Some(
                        crate::mangle::apply_mangle(vm, &mangled_version)
                            .map_err(|e| DiscoveryError::PatternError(e.to_string()))?,
                    )
                } else {
                    None
                };

                releases.push(Release::new_full(
                    mangled_version,
                    mangled_url,
                    pgpsigurl,
                    target_filename,
                    package_version,
                ));
            }

            Ok(releases)
        }
    }

    /// Discover all available releases for this watch entry (blocking version)
    ///
    /// This is the blocking version of `discover()`. Requires the 'blocking' feature.
    #[cfg(feature = "blocking")]
    fn discover_blocking(
        &self,
        package: impl FnOnce() -> String,
    ) -> Result<Vec<Release>, DiscoveryError>
    where
        Self: Sized,
    {
        self.discover_blocking_impl(package, None)
    }

    /// Discover all available releases with a custom HTTP client (blocking version)
    #[cfg(feature = "blocking")]
    fn discover_blocking_with_client(
        &self,
        package: impl FnOnce() -> String,
        client: &reqwest::blocking::Client,
    ) -> Result<Vec<Release>, DiscoveryError>
    where
        Self: Sized,
    {
        self.discover_blocking_impl(package, Some(client))
    }

    /// Internal implementation for blocking discover
    #[cfg(feature = "blocking")]
    fn discover_blocking_impl(
        &self,
        package: impl FnOnce() -> String,
        client: Option<&reqwest::blocking::Client>,
    ) -> Result<Vec<Release>, DiscoveryError>
    where
        Self: Sized,
    {
        // Get the URL and apply package substitution
        let url = self
            .format_url(package)
            .map_err(|e| DiscoveryError::UrlError(e.to_string()))?;

        // Get user agent
        let user_agent = self
            .user_agent()
            .unwrap_or_else(|| DEFAULT_USER_AGENT.to_string());

        // Build HTTP client if not provided
        let default_client;
        let http_client = if let Some(c) = client {
            c
        } else {
            default_client = reqwest::blocking::Client::builder()
                .user_agent(user_agent)
                .build()
                .map_err(|e| DiscoveryError::HttpError(e.to_string()))?;
            &default_client
        };

        // Fetch the URL
        let response = http_client
            .get(url.as_str())
            .send()
            .map_err(|e| DiscoveryError::HttpError(e.to_string()))?;

        let body = response
            .bytes()
            .map_err(|e| DiscoveryError::HttpError(e.to_string()))?;

        // Apply pagemangle if present
        let mangled_body = if let Some(mangle) = self.pagemangle() {
            let page_str = String::from_utf8_lossy(&body);
            let result = crate::mangle::apply_mangle(&mangle, &page_str)
                .map_err(|e| DiscoveryError::PatternError(e.to_string()))?;
            result.into_bytes()
        } else {
            body.to_vec()
        };

        // Get the matching pattern
        let matching_pattern = self
            .matching_pattern()
            .ok_or_else(|| DiscoveryError::MissingField("matching_pattern".to_string()))?;

        // Apply substitution to the matching pattern
        let package_name = String::new();
        let pattern = crate::subst::subst(&matching_pattern, || package_name.clone());

        // Determine search mode
        let searchmode = self
            .searchmode()
            .map_err(|e| DiscoveryError::PatternError(e.to_string()))?;
        let searchmode_str = searchmode.to_string();

        // Search for versions
        let results = crate::search::search(
            &searchmode_str,
            std::io::Cursor::new(mangled_body.as_ref() as &[u8]),
            &pattern,
            &package_name,
            url.as_str(),
        )?;

        // Apply mangles to each result and convert to Release objects
        let mut releases = Vec::new();
        for (version, full_url) in results {
            // Apply uversionmangle
            let mangled_version = if let Some(mangle) = self.uversionmangle() {
                crate::mangle::apply_mangle(&mangle, &version)
                    .map_err(|e| DiscoveryError::PatternError(e.to_string()))?
            } else {
                version
            };

            // Apply downloadurlmangle
            let mangled_url = if let Some(mangle) = self.downloadurlmangle() {
                crate::mangle::apply_mangle(&mangle, &full_url)
                    .map_err(|e| DiscoveryError::PatternError(e.to_string()))?
            } else {
                full_url
            };

            // Apply pgpsigurlmangle if present
            let pgpsigurl = if let Some(mangle) = self.pgpsigurlmangle() {
                Some(
                    crate::mangle::apply_mangle(&mangle, &mangled_url)
                        .map_err(|e| DiscoveryError::PatternError(e.to_string()))?,
                )
            } else {
                None
            };

            // Apply filenamemangle if present
            let target_filename = if let Some(mangle) = self.filenamemangle() {
                Some(
                    crate::mangle::apply_mangle(&mangle, &mangled_url)
                        .map_err(|e| DiscoveryError::PatternError(e.to_string()))?,
                )
            } else {
                None
            };

            // Apply oversionmangle if present
            let package_version = if let Some(mangle) = self.oversionmangle() {
                Some(
                    crate::mangle::apply_mangle(&mangle, &mangled_version)
                        .map_err(|e| DiscoveryError::PatternError(e.to_string()))?,
                )
            } else {
                None
            };

            releases.push(Release::new_full(
                mangled_version,
                mangled_url,
                pgpsigurl,
                target_filename,
                package_version,
            ));
        }

        Ok(releases)
    }
}

/// Trait for discovering releases from all entries in a watch file
pub trait DiscoverAll: WatchFileFormat {
    /// Discover releases from all entries in the watch file (async version)
    ///
    /// # Arguments
    ///
    /// * `package` - Closure that returns the package name to use for substitution in URLs
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use debian_watch::WatchFile;
    /// use debian_watch::discover::DiscoverAll;
    ///
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let wf: WatchFile = r#"version=4
    /// https://example.com/files .*/v?(\\d\\S+)\\.tar\\.gz
    /// "#.parse()?;
    ///
    /// let all_releases = wf.discover_all(|| "mypackage".to_string()).await?;
    /// for (entry_idx, releases) in all_releases.iter().enumerate() {
    ///     println!("Entry {}: {} releases found", entry_idx, releases.len());
    /// }
    /// # Ok(())
    /// # }
    /// ```
    fn discover_all(
        &self,
        package: impl Fn() -> String + Send + Clone + 'static,
    ) -> impl std::future::Future<Output = Result<Vec<Vec<Release>>, DiscoveryError>> + Send
    where
        Self::Entry: Discover + Send + 'static,
    {
        // Collect entries before async block to avoid holding self reference
        let entries: Vec<_> = self.entries().collect();

        async move {
            let mut all_releases = Vec::new();
            for entry in entries {
                let pkg = package.clone();
                let releases = entry.discover(move || pkg()).await?;
                all_releases.push(releases);
            }
            Ok(all_releases)
        }
    }

    /// Discover releases from all entries in the watch file (blocking version)
    #[cfg(feature = "blocking")]
    fn discover_all_blocking(
        &self,
        package: impl Fn() -> String,
    ) -> Result<Vec<Vec<Release>>, DiscoveryError>
    where
        Self::Entry: Discover,
    {
        let mut all_releases = Vec::new();
        for entry in self.entries() {
            let releases = entry.discover_blocking(&package)?;
            all_releases.push(releases);
        }
        Ok(all_releases)
    }
}

// Blanket implementation: any WatchEntry implements Discover
impl<T: WatchEntry> Discover for T {}

// Blanket implementation: any WatchFileFormat implements DiscoverAll
impl<T: WatchFileFormat> DiscoverAll for T {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_discovery_error_display() {
        let err = DiscoveryError::MissingField("url".to_string());
        assert_eq!(err.to_string(), "Missing field: url");

        let err = DiscoveryError::PatternError("invalid regex".to_string());
        assert_eq!(err.to_string(), "Pattern error: invalid regex");
    }
}
