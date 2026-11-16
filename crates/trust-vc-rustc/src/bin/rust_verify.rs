//! `rust_verify`: the binary upstream Verus's test harness runs from
//! `target-verus/<profile>/`. All logic lives in `trust_vc_rustc::shim`.

// Linking librustc_driver requires the final binary to opt in as well.
#![feature(rustc_private)]

fn main() -> std::process::ExitCode {
    // SAFETY: first native-entry operation, before argument handling, file opens,
    // compiler callbacks, or host worker threads can reuse inherited descriptors.
    if let Err(exit) = unsafe { trust_vc_rustc::native_entry::capture_inherited_resources() } {
        return exit;
    }
    trust_vc_rustc::shim::main()
}
