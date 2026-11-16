//! Native Trust entrypoint selected by cargo-verus's sibling lookup.
//!
//! Preserve the same CLI, Cargo protocol, macro context and exit status as
//! rust_verify. The linked Trust compiler handles the request directly.

#![feature(rustc_private)]

fn main() -> std::process::ExitCode {
    // SAFETY: first native-entry operation, before argument handling, file opens,
    // compiler callbacks, or host worker threads can reuse inherited descriptors.
    if let Err(exit) = unsafe { trust_vc_rustc::native_entry::capture_inherited_resources() } {
        return exit;
    }
    trust_vc_rustc::shim::main()
}
