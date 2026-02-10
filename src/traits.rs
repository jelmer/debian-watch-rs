use crate::types::*;

/// Common trait for all watch file format versions
pub trait WatchFileFormat {
    /// The type used to represent individual watch entries
    type Entry: WatchEntry;

    /// Returns the version of the watch file (1-5)
    fn version(&self) -> u32;

    /// Returns an iterator over all entries in the watch file
    fn entries(&self) -> Box<dyn Iterator<Item = Self::Entry> + '_>;

    /// Convert the watch file back to its string representation
    fn format_string(&self) -> String;
}

/// Common trait for watch file entries across all formats
pub trait WatchEntry {
    /// Returns the URL of the entry
    fn url(&self) -> String;

    /// Returns the matching pattern of the entry
    fn matching_pattern(&self) -> Option<String>;

    /// Returns the version policy
    fn version_policy(&self) -> Result<Option<crate::VersionPolicy>, ParseError>;

    /// Returns the script of the entry
    fn script(&self) -> Option<String>;

    /// Get the value of a generic option by key
    fn get_option(&self, key: &str) -> Option<String>;

    /// Check if an option is set
    fn has_option(&self, key: &str) -> bool;

    // Commonly used options - delegated to get_option() but typed

    /// The name of the secondary source tarball
    fn component(&self) -> Option<String> {
        self.get_option("component")
    }

    /// Component type
    fn ctype(&self) -> Result<Option<ComponentType>, ParseError> {
        self.get_option("ctype").map(|s| s.parse()).transpose()
    }

    /// Compression method
    fn compression(&self) -> Result<Option<Compression>, ParseError> {
        self.get_option("compression")
            .map(|s| s.parse())
            .transpose()
    }

    /// Repack the tarball
    fn repack(&self) -> bool {
        self.has_option("repack")
    }

    /// Repack suffix
    fn repacksuffix(&self) -> Option<String> {
        self.get_option("repacksuffix")
    }

    /// Retrieve the mode of the watch file entry
    fn mode(&self) -> Result<Mode, ParseError> {
        Ok(self
            .get_option("mode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the git pretty mode
    fn pretty(&self) -> Result<Pretty, ParseError> {
        Ok(self
            .get_option("pretty")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Set the date string used by the pretty option
    fn date(&self) -> String {
        self.get_option("date").unwrap_or_else(|| "%Y%m%d".into())
    }

    /// Return the git export mode
    fn gitexport(&self) -> Result<GitExport, ParseError> {
        Ok(self
            .get_option("gitexport")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the git mode
    fn gitmode(&self) -> Result<GitMode, ParseError> {
        Ok(self
            .get_option("gitmode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the pgp mode
    fn pgpmode(&self) -> Result<PgpMode, ParseError> {
        Ok(self
            .get_option("pgpmode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the search mode
    fn searchmode(&self) -> Result<SearchMode, ParseError> {
        Ok(self
            .get_option("searchmode")
            .map(|s| s.parse())
            .transpose()?
            .unwrap_or_default())
    }

    /// Return the decompression mode
    fn decompress(&self) -> bool {
        self.has_option("decompress")
    }

    /// Whether to disable all site specific special case code
    fn bare(&self) -> bool {
        self.has_option("bare")
    }

    /// Set the user-agent string
    fn user_agent(&self) -> Option<String> {
        self.get_option("user-agent")
    }

    /// Use PASV mode for the FTP connection
    fn passive(&self) -> Option<bool> {
        if self.has_option("passive") || self.has_option("pasv") {
            Some(true)
        } else if self.has_option("active") || self.has_option("nopasv") {
            Some(false)
        } else {
            None
        }
    }

    /// Extra options to use with the unzip command
    fn unzipoptions(&self) -> Option<String> {
        self.get_option("unzipopt")
    }

    /// Normalize the downloaded web page string
    fn dversionmangle(&self) -> Option<String> {
        self.get_option("dversionmangle")
    }

    /// Mangle the upstream version
    fn uversionmangle(&self) -> Option<String> {
        self.get_option("uversionmangle")
    }

    /// Mangle the download URL
    fn downloadurlmangle(&self) -> Option<String> {
        self.get_option("downloadurlmangle")
    }

    /// Mangle the filename
    fn filenamemangle(&self) -> Option<String> {
        self.get_option("filenamemangle")
    }

    /// Mangle the PGP signature URL
    fn pgpsigurlmangle(&self) -> Option<String> {
        self.get_option("pgpsigurlmangle")
    }

    /// Mangle the oversionmangle
    fn oversionmangle(&self) -> Option<String> {
        self.get_option("oversionmangle")
    }

    /// Mangle the page content
    fn pagemangle(&self) -> Option<String> {
        self.get_option("pagemangle")
    }

    /// Mangle the directory version
    fn dirversionmangle(&self) -> Option<String> {
        self.get_option("dirversionmangle")
    }

    /// Mangle the version
    fn versionmangle(&self) -> Option<String> {
        self.get_option("versionmangle")
    }

    /// Decode hrefs before matching
    fn hrefdecode(&self) -> Option<bool> {
        self.get_option("hrefdecode")
            .map(|s| s == "1" || s == "yes")
    }

    /// Replace all substitutions and return the resulting URL
    fn format_url(&self, package: impl FnOnce() -> String) -> Result<url::Url, url::ParseError> {
        crate::subst::subst(self.url().as_str(), package).parse()
    }
}
