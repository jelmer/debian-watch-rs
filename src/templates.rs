//! Template expansion for v5 watch files
//!
//! This module provides template expansion for common project hosting platforms,
//! simplifying watch file creation by auto-generating Source URLs, matching patterns,
//! and other configuration based on template type.
//!
//! # Supported Templates
//!
//! - `GitHub` - For GitHub-hosted projects
//! - `GitLab` - For GitLab instances
//! - `PyPI` - For Python packages on PyPI
//! - `Npmregistry` - For npm packages
//! - `Metacpan` - For Perl modules on MetaCPAN

/// Error type for template expansion
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TemplateError {
    /// Unknown template type
    UnknownTemplate(String),
    /// Missing required field
    MissingField {
        /// Template type
        template: String,
        /// Field name
        field: String,
    },
    /// Invalid field value
    InvalidValue {
        /// Field name
        field: String,
        /// Reason for invalidity
        reason: String,
    },
}

impl std::fmt::Display for TemplateError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TemplateError::UnknownTemplate(t) => write!(f, "Unknown template type: {}", t),
            TemplateError::MissingField { template, field } => {
                write!(f, "{} template requires '{}' field", template, field)
            }
            TemplateError::InvalidValue { field, reason } => {
                write!(f, "Invalid value for '{}': {}", field, reason)
            }
        }
    }
}

impl std::error::Error for TemplateError {}

/// Template with variant-specific parameters
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Template {
    /// GitHub template
    GitHub {
        /// Project owner
        owner: String,
        /// Project repository name
        repository: String,
        /// Search only releases (not all tags)
        release_only: bool,
        /// Version type pattern to use
        version_type: Option<String>,
    },
    /// GitLab template
    GitLab {
        /// Project URL
        dist: String,
        /// Search only releases (not all tags)
        release_only: bool,
        /// Version type pattern to use
        version_type: Option<String>,
    },
    /// PyPI template
    PyPI {
        /// Package name
        package: String,
        /// Version type pattern to use
        version_type: Option<String>,
    },
    /// npm registry template
    Npmregistry {
        /// Package name (may include @scope/)
        package: String,
        /// Version type pattern to use
        version_type: Option<String>,
    },
    /// MetaCPAN template
    Metacpan {
        /// Distribution name (using :: or -)
        dist: String,
        /// Version type pattern to use
        version_type: Option<String>,
    },
}

/// Expanded template fields
#[derive(Debug, Clone, Default)]
pub struct ExpandedTemplate {
    /// Source URL
    pub source: Option<String>,
    /// Matching pattern
    pub matching_pattern: Option<String>,
    /// Search mode
    pub searchmode: Option<String>,
    /// Mode
    pub mode: Option<String>,
    /// PGP mode
    pub pgpmode: Option<String>,
    /// Download URL mangle
    pub downloadurlmangle: Option<String>,
}

/// Expand a template into field values
pub fn expand_template(template: Template) -> ExpandedTemplate {
    match template {
        Template::GitHub {
            owner,
            repository,
            release_only,
            version_type,
        } => expand_github_template(owner, repository, release_only, version_type),
        Template::GitLab {
            dist,
            release_only,
            version_type,
        } => expand_gitlab_template(dist, release_only, version_type),
        Template::PyPI {
            package,
            version_type,
        } => expand_pypi_template(package, version_type),
        Template::Npmregistry {
            package,
            version_type,
        } => expand_npmregistry_template(package, version_type),
        Template::Metacpan { dist, version_type } => expand_metacpan_template(dist, version_type),
    }
}

/// Expand GitHub template
fn expand_github_template(
    owner: String,
    repository: String,
    release_only: bool,
    version_type: Option<String>,
) -> ExpandedTemplate {
    let version_pattern = version_type
        .as_deref()
        .map(|v| format!("@{}@", v))
        .unwrap_or_else(|| "@ANY_VERSION@".to_string());

    let source = if release_only {
        format!("https://github.com/{}/{}/releases", owner, repository)
    } else {
        format!("https://github.com/{}/{}/tags", owner, repository)
    };

    let matching_pattern = format!(
        r".*/(?:refs/tags/)?v?{}{}",
        version_pattern, "@ARCHIVE_EXT@"
    );

    ExpandedTemplate {
        source: Some(source),
        matching_pattern: Some(matching_pattern),
        searchmode: Some("html".to_string()),
        ..Default::default()
    }
}

/// Expand GitLab template
fn expand_gitlab_template(
    dist: String,
    _release_only: bool,
    version_type: Option<String>,
) -> ExpandedTemplate {
    let version_pattern = version_type
        .as_deref()
        .map(|v| format!("@{}@", v))
        .unwrap_or_else(|| "@ANY_VERSION@".to_string());

    // GitLab uses mode=gitlab
    ExpandedTemplate {
        source: Some(dist),
        matching_pattern: Some(format!(r".*/v?{}{}", version_pattern, "@ARCHIVE_EXT@")),
        mode: Some("gitlab".to_string()),
        ..Default::default()
    }
}

/// Expand PyPI template
fn expand_pypi_template(package: String, version_type: Option<String>) -> ExpandedTemplate {
    let version_pattern = version_type
        .as_deref()
        .map(|v| format!("@{}@", v))
        .unwrap_or_else(|| "@ANY_VERSION@".to_string());

    ExpandedTemplate {
        source: Some(format!("https://pypi.debian.net/{}/", package)),
        matching_pattern: Some(format!(
            r"https://pypi\.debian\.net/{}/[^/]+\.tar\.gz#/.*-{}\.tar\.gz",
            package, version_pattern
        )),
        searchmode: Some("plain".to_string()),
        ..Default::default()
    }
}

/// Expand Npmregistry template
fn expand_npmregistry_template(package: String, version_type: Option<String>) -> ExpandedTemplate {
    let version_pattern = version_type
        .as_deref()
        .map(|v| format!("@{}@", v))
        .unwrap_or_else(|| "@ANY_VERSION@".to_string());

    // npm package names might have @ prefix for scoped packages
    let package_name = package.trim_start_matches('@');

    ExpandedTemplate {
        source: Some(format!("https://registry.npmjs.org/{}", package)),
        matching_pattern: Some(format!(
            r"https://registry\.npmjs\.org/{}/-/.*-{}@ARCHIVE_EXT@",
            package_name.replace('/', r"\/"),
            version_pattern
        )),
        searchmode: Some("plain".to_string()),
        ..Default::default()
    }
}

/// Expand Metacpan template
fn expand_metacpan_template(dist: String, version_type: Option<String>) -> ExpandedTemplate {
    let version_pattern = version_type
        .as_deref()
        .map(|v| format!("@{}@", v))
        .unwrap_or_else(|| "@ANY_VERSION@".to_string());

    // MetaCPAN dist names can use :: or -
    let dist_name = dist.replace("::", "-");

    ExpandedTemplate {
        source: Some("https://cpan.metacpan.org/authors/id/".to_string()),
        matching_pattern: Some(format!(r".*/{}{}@ARCHIVE_EXT@", dist_name, version_pattern)),
        searchmode: Some("plain".to_string()),
        ..Default::default()
    }
}

/// Parse GitHub URL or owner/repository to extract owner and repository
pub fn parse_github_url(url: &str) -> Result<(String, String), TemplateError> {
    let url = url.trim_end_matches('/');

    // Try to parse as URL
    if let Ok(parsed) = url::Url::parse(url) {
        if parsed.host_str() == Some("github.com") {
            let path = parsed.path().trim_start_matches('/').trim_end_matches('/');
            let parts: Vec<&str> = path.split('/').collect();
            if parts.len() >= 2 {
                return Ok((parts[0].to_string(), parts[1].to_string()));
            }
        }
    }

    // Try to parse as owner/repository
    let parts: Vec<&str> = url.split('/').collect();
    if parts.len() == 2 {
        return Ok((parts[0].to_string(), parts[1].to_string()));
    }

    Err(TemplateError::InvalidValue {
        field: "Dist".to_string(),
        reason: format!("Could not parse GitHub URL: {}", url),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_github_template_with_owner_repository() {
        let template = Template::GitHub {
            owner: "torvalds".to_string(),
            repository: "linux".to_string(),
            release_only: false,
            version_type: None,
        };

        let result = expand_template(template);
        assert_eq!(
            result.source,
            Some("https://github.com/torvalds/linux/tags".to_string())
        );
        assert_eq!(
            result.matching_pattern,
            Some(r".*/(?:refs/tags/)?v?@ANY_VERSION@@ARCHIVE_EXT@".to_string())
        );
    }

    #[test]
    fn test_github_template_release_only() {
        let template = Template::GitHub {
            owner: "test".to_string(),
            repository: "project".to_string(),
            release_only: true,
            version_type: None,
        };

        let result = expand_template(template);
        assert_eq!(
            result.source,
            Some("https://github.com/test/project/releases".to_string())
        );
    }

    #[test]
    fn test_parse_github_url() {
        let (owner, repo) = parse_github_url("https://github.com/guimard/llng-docker").unwrap();
        assert_eq!(owner, "guimard");
        assert_eq!(repo, "llng-docker");

        let (owner, repo) = parse_github_url("torvalds/linux").unwrap();
        assert_eq!(owner, "torvalds");
        assert_eq!(repo, "linux");
    }

    #[test]
    fn test_pypi_template() {
        let template = Template::PyPI {
            package: "bitbox02".to_string(),
            version_type: None,
        };

        let result = expand_template(template);
        assert_eq!(
            result.source,
            Some("https://pypi.debian.net/bitbox02/".to_string())
        );
        assert_eq!(result.searchmode, Some("plain".to_string()));
    }

    #[test]
    fn test_npmregistry_template() {
        let template = Template::Npmregistry {
            package: "@lemonldapng/handler".to_string(),
            version_type: None,
        };

        let result = expand_template(template);
        assert_eq!(
            result.source,
            Some("https://registry.npmjs.org/@lemonldapng/handler".to_string())
        );
        assert_eq!(result.searchmode, Some("plain".to_string()));
    }

    #[test]
    fn test_gitlab_template() {
        let template = Template::GitLab {
            dist: "https://salsa.debian.org/debian/devscripts".to_string(),
            release_only: false,
            version_type: None,
        };

        let result = expand_template(template);
        assert_eq!(
            result.source,
            Some("https://salsa.debian.org/debian/devscripts".to_string())
        );
        assert_eq!(result.mode, Some("gitlab".to_string()));
    }

    #[test]
    fn test_metacpan_template() {
        let template = Template::Metacpan {
            dist: "MetaCPAN-Client".to_string(),
            version_type: None,
        };

        let result = expand_template(template);
        assert_eq!(
            result.source,
            Some("https://cpan.metacpan.org/authors/id/".to_string())
        );
    }
}
