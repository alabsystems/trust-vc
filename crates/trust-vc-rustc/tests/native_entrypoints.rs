//! Exercise both genuine Cargo-built native executable targets.

#![feature(rustc_private)]

use std::process::{Command, Output};

fn invoke(binary: &str, arguments: &[&str]) -> Output {
    Command::new(binary)
        .args(arguments)
        .env(trust_vc_rustc::cargo::VIA_CARGO, "1")
        .output()
        .expect("run the genuine native executable")
}

#[test]
fn cargo_probe_and_invalid_protocol_use_the_same_native_entrypoint() {
    let binaries = [
        env!("CARGO_BIN_EXE_rust_verify"),
        env!("CARGO_BIN_EXE_verus"),
    ];
    let probe =
        binaries.map(|binary| invoke(binary, &["trustc", "--crate-name=___", "--print=cfg"]));
    for output in &probe {
        assert!(output.status.success(), "{output:?}");
        assert!(String::from_utf8_lossy(&output.stdout).contains("target_pointer_width="));
    }
    assert_eq!(probe[0].stdout, probe[1].stdout);
    assert_eq!(probe[0].stderr, probe[1].stderr);

    let invalid = binaries.map(|binary| invoke(binary, &["--print=cfg"]));
    for output in &invalid {
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("bad-arguments"));
    }
    assert_eq!(invalid[0].stdout, invalid[1].stdout);
    assert_eq!(invalid[0].stderr, invalid[1].stderr);
}
