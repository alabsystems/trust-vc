//! `rust_verify`: the binary upstream Verus's test harness runs from
//! `target-verus/<profile>/`. All logic lives in `trust_vc_rustc::shim`.

// Linking librustc_driver requires the final binary to opt in as well.
#![feature(rustc_private)]

fn main() -> std::process::ExitCode {
    trust_vc_rustc::shim::main()
}
