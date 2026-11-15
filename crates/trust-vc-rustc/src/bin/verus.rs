//! Native Trust entrypoint selected by cargo-verus's sibling lookup.
//!
//! Preserve the same CLI, Cargo protocol, macro context and exit status as
//! rust_verify. The linked Trust compiler handles the request directly.

#![feature(rustc_private)]

fn main() -> std::process::ExitCode {
    trust_vc_rustc::shim::main()
}
