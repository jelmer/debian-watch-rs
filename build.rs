fn main() {
    // Ensure at least one format feature is enabled
    let has_linebased = cfg!(feature = "linebased");
    let has_deb822 = cfg!(feature = "deb822");

    if !has_linebased && !has_deb822 {
        panic!(
            "At least one watch file format must be enabled.\n\
             Enable either 'linebased' (for v1-4 format) or 'deb822' (for v5 format).\n\
             Example: cargo build --features linebased"
        );
    }
}
