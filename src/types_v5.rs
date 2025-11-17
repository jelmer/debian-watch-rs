use crate::parse_v5::{EntryV5, WatchFileV5};
use crate::traits::{WatchEntry, WatchFileFormat};
use crate::types::ParseError;
use crate::VersionPolicy;

impl WatchFileFormat for WatchFileV5 {
    type Entry = EntryV5;

    fn version(&self) -> u32 {
        self.version()
    }

    fn entries(&self) -> Box<dyn Iterator<Item = Self::Entry> + '_> {
        Box::new(WatchFileV5::entries(self))
    }

    fn to_string(&self) -> String {
        ToString::to_string(self)
    }
}

impl WatchEntry for EntryV5 {
    fn url(&self) -> String {
        // In format 5, the URL is in the "Source" field
        self.source().unwrap_or_default()
    }

    fn matching_pattern(&self) -> Option<String> {
        self.matching_pattern_v5()
    }

    fn version_policy(&self) -> Result<Option<VersionPolicy>, ParseError> {
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
