// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! CONTAMINATION probe for the isolated-termination-query memo.
//!
//! The memo lives in a thread-local keyed by
//! `VerificationContext::isolated_query_key`. Its cardinal failure mode is
//! serving one cycle's verdict to a DIFFERENT cycle, which would let a
//! non-shrinking recursive definition buy the body axiom a well-founded one
//! earned. `--test-threads=1` puts every test in this binary on the same thread,
//! so the memo really is shared across them — that is the point.
//!
//! Each `warmup` is informational (it only has to populate the memo). Each
//! `exploit` returns 0 while claiming `result == 1` and must NEVER verify.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fx() -> String {
    format!(
        "{}/tests/data/termination_memo_contamination.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verdict(func: &str) -> Result<VerifyResult, String> {
    let start = std::time::Instant::now();
    let result = verify_function_from_file(&fx(), func).map_err(|err| err.to_string());
    eprintln!("[{func}] {:.2}s {result:?}", start.elapsed().as_secs_f64());
    result
}

#[test]
fn a1_warmup_populates_the_memo() {
    let result = verdict("memo_warmup");
    eprintln!("warmup verdict (informational): {result:?}");
}

#[test]
fn a2_non_shrinking_cycle_still_refuses_after_a_well_founded_one() {
    let result = verdict("memo_exploit");
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "CARDINAL: `bad(n) == bad(n) + 1` is contradictory, so its body axiom must \
         never be published. Verifying `memo_exploit` means the non-shrinking cycle \
         was served the well-founded cycle's memo entry. Got: {result:?}"
    );
}

#[test]
fn a3_twin_warmup_populates_the_memo() {
    let result = verdict("twin_warmup");
    eprintln!("twin warmup verdict (informational): {result:?}");
}

#[test]
fn a4_twin_non_shrinking_cycle_still_refuses() {
    let result = verdict("twin_exploit");
    assert!(
        !matches!(result, Ok(VerifyResult::Verified)),
        "CARDINAL: `t2(n)` does not shrink its measure; verifying `twin_exploit` \
         means the memo (or Stage 2) admitted it. Got: {result:?}"
    );
}
