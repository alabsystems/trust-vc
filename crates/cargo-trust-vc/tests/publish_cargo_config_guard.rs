// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression coverage for export transform T2 (`publish/transforms.sh`): the
//! public `.cargo/config.toml` carries no verification flag. Trust's
//! CLAUDE.md, "Consuming repos", forbids `-Ztrust-verify=off` in
//! `build.rustflags` (the key applies to every toolchain and stable rustc
//! rejects it); the Targo lane owns activation and unit scope.
//!
//! These tests run T2's own shell text, cut out of `publish/transforms.sh`,
//! against a scratch export. `publish/` is not part of the public snapshot
//! (publish/manifest.txt), so in an export tree, where the directory is
//! absent, each test says so on stderr and returns without asserting.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

/// The blanket off-switch `publish/public-cargo-config.toml` carried until
/// 2026-09-28.
const OFF_SWITCH_CONFIG: &str = "[build]\n\
rustflags = [\"-Ztrust-verify=off\"]\n\
rustdocflags = [\"-Ztrust-verify=off\"]\n\
\n\
[net]\n\
git-fetch-with-cli = true\n";

fn publish_dir() -> Option<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../publish");
    if dir.join("transforms.sh").is_file() {
        Some(dir)
    } else {
        eprintln!(
            "publish/transforms.sh is absent (a public snapshot ships no publish/); \
             T2 guard not exercised"
        );
        None
    }
}

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    let sequence = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "cargo_trust_vc_publish_t2_{label}_{}_{}_{}",
        std::process::id(),
        unique,
        sequence
    ))
}

/// T2's block: from its `# ── T2` banner up to the next `# ── T` banner (or
/// the end of the file).
fn t2_block(transforms: &str) -> String {
    let start = transforms
        .find("# ── T2")
        .expect("publish/transforms.sh should carry a `# ── T2` section");
    let rest = &transforms[start..];
    let end = rest[1..]
        .find("\n# ── T")
        .map(|offset| offset + 2)
        .unwrap_or(rest.len());
    rest[..end].to_string()
}

/// Run T2 with `config` as `publish/public-cargo-config.toml`, the way the
/// publication engine sources it: `fail` exits non-zero, `note` is quiet.
fn run_t2(publish: &Path, label: &str, config: &str) -> Output {
    let transforms = std::fs::read_to_string(publish.join("transforms.sh"))
        .expect("publish/transforms.sh should be readable");
    let root = temp_dir(label);
    let pub_dir = root.join("publish");
    let export = root.join("export");
    std::fs::create_dir_all(&pub_dir).expect("scratch publish dir should be creatable");
    std::fs::create_dir_all(&export).expect("scratch export dir should be creatable");
    std::fs::write(pub_dir.join("public-cargo-config.toml"), config)
        .expect("scratch public config should be written");
    let script = format!(
        "fail() {{ printf 'FAIL: %s\\n' \"$*\" >&2; exit 1; }}\n\
         note() {{ :; }}\n\
         {}\n\
         exit 0\n",
        t2_block(&transforms)
    );
    let output = Command::new("bash")
        .arg("-c")
        .arg(script)
        .env("PUB", &pub_dir)
        .env("EXPORT", &export)
        .output()
        .expect("bash should run the T2 block");
    std::fs::remove_dir_all(&root).ok();
    output
}

#[test]
fn committed_public_cargo_config_passes_t2() {
    let Some(publish) = publish_dir() else {
        return;
    };
    let config = std::fs::read_to_string(publish.join("public-cargo-config.toml"))
        .expect("publish/public-cargo-config.toml should be readable");
    let output = run_t2(&publish, "committed", &config);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "T2 should install the committed public config: {stderr}"
    );
}

#[test]
fn committed_public_cargo_config_sets_no_trust_flag() {
    let Some(publish) = publish_dir() else {
        return;
    };
    let config = std::fs::read_to_string(publish.join("public-cargo-config.toml"))
        .expect("publish/public-cargo-config.toml should be readable");
    for line in config.lines() {
        if line.trim_start().starts_with('#') {
            continue;
        }
        assert!(
            !line.contains("-Ztrust") && !line.contains("-Z trust"),
            "public cargo config sets a -Ztrust flag outside a comment: {line}"
        );
        assert!(
            !line.trim_start().starts_with("rustflags")
                && !line.trim_start().starts_with("rustdocflags"),
            "public cargo config sets build flags: {line}"
        );
    }
}

#[test]
fn t2_refuses_a_public_config_that_switches_verification_off() {
    let Some(publish) = publish_dir() else {
        return;
    };
    let output = run_t2(&publish, "off_switch", OFF_SWITCH_CONFIG);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "T2 must refuse a config carrying -Ztrust-verify=off: {stderr}"
    );
    assert!(
        stderr.contains("FAIL: T2: public cargo config sets a -Ztrust flag"),
        "{stderr}"
    );

    // A spaced `-Z trust-...` is the same flag.
    let spaced = OFF_SWITCH_CONFIG.replace("-Ztrust", "-Z trust");
    let output = run_t2(&publish, "off_switch_spaced", &spaced);
    assert!(
        !output.status.success(),
        "T2 must refuse `-Z trust-verify=off` too: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn t2_ignores_a_trust_flag_named_only_in_a_comment() {
    let Some(publish) = publish_dir() else {
        return;
    };
    let config = "# This file used to carry `-Ztrust-verify=off`; it no longer does.\n\
                  [net]\n\
                  git-fetch-with-cli = true\n";
    let output = run_t2(&publish, "comment", config);
    assert!(
        output.status.success(),
        "a comment naming the flag is not a flag: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
