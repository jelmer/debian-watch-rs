//! Variable substitution for watch file patterns

const SUBSTITUTIONS: &[(&str, &str)] = &[
    // This is substituted with the source package name found in the first line
    // of the debian/changelog file.
    // "@PACKAGE@": None,
    // This is substituted by the legal upstream version regex (capturing).
    ("@ANY_VERSION@", r"[-_]?(\d[\-+\.:\~\da-zA-Z]*)"),
    // This is substituted by the typical archive file extension regex
    // (non-capturing).
    (
        "@ARCHIVE_EXT@",
        r"(?i)\.(?:tar\.xz|tar\.bz2|tar\.gz|zip|tgz|tbz|txz)",
    ),
    // This is substituted by the typical signature file extension regex
    // (non-capturing).
    (
        "@SIGNATURE_EXT@",
        r"(?i)\.(?:tar\.xz|tar\.bz2|tar\.gz|zip|tgz|tbz|txz)\.(?:asc|pgp|gpg|sig|sign)",
    ),
    // This is substituted by the typical Debian extension regexp (capturing).
    ("@DEB_EXT@", r"[\+~](debian|dfsg|ds|deb)(\.)?(\d+)?$"),
];

/// Substitute watch file variables like @PACKAGE@ and @ANY_VERSION@
pub fn subst(text: &str, package: impl FnOnce() -> String) -> String {
    // Early return if no substitutions are needed
    if !text.contains('@') {
        return text.to_string();
    }

    // Apply all substitutions in a single pass using fold
    let result = SUBSTITUTIONS
        .iter()
        .fold(text.to_string(), |acc, (pattern, replacement)| {
            acc.replace(pattern, replacement)
        });

    // Handle @PACKAGE@ substitution if needed
    if result.contains("@PACKAGE@") {
        let package_name = package();
        result.replace("@PACKAGE@", &package_name)
    } else {
        result
    }
}

#[test]
fn test_subst() {
    assert_eq!(
        subst("@ANY_VERSION@", || unreachable!()),
        r"[-_]?(\d[\-+\.:\~\da-zA-Z]*)"
    );
    assert_eq!(subst("@PACKAGE@", || "foo".to_string()), "foo");
}
