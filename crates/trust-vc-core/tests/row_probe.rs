// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Shared, reusable probe harness for the capability re-audit. Reads a fixture
//! path and a function name from env vars, verifies (cache-off), and prints a
//! one-line verdict. ONE test binary reused by every re-audit agent — avoids the
//! disk exhaustion that many distinct `--test` binaries cause.
//!
//! Usage:  TVC_PROBE_FILE=/tmp/x.rs TVC_PROBE_FN=foo \
//!           targo test -p trust-vc-core --test row_probe -- --nocapture

use trust_vc_core::{verify_function_from_file, VerifyResult};

#[test]
fn probe() {
    let _env_lock = trust_vc_core::env::lock_env();
    let _vc_cache = trust_vc_core::env::ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    let file = match std::env::var("TVC_PROBE_FILE") {
        Ok(f) => f,
        Err(_) => {
            println!("PROBE_VERDICT[]=SKIP(no TVC_PROBE_FILE)");
            return;
        }
    };
    let func = std::env::var("TVC_PROBE_FN").unwrap_or_default();
    let r = verify_function_from_file(&file, &func).unwrap_or_else(|e| VerifyResult::Error {
        message: e.to_string(),
    });
    let verdict = match &r {
        VerifyResult::Verified => "VERIFIED".to_string(),
        VerifyResult::Counterexample { .. } => "COUNTEREXAMPLE".to_string(),
        VerifyResult::Error { message } => {
            format!("ERROR:{}", message.chars().take(90).collect::<String>())
        }
        other => {
            // NotProved / Unknown / any future variant — Debug head.
            let d = format!("{other:?}");
            let head: String = d.chars().take(24).collect();
            format!("CLOSED:{head}")
        }
    };
    println!("PROBE_VERDICT[{func}]={verdict}");
}
