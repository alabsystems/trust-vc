// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! RE-KEYED AT THE wCLO MERGE, and now NON-VACUOUS for the first time. This
//! file began as a ROUND-9 RESIDUAL RATCHET recording a defect it did not fix.
//! Both halves of that defect are now fixed, on two different branches, and
//! this file pins the conjunction that neither branch could pin alone.
//!
//! THE DEFECT, HALF ONE (scope, fixed on `work/wCONST`). `ScopeScan`
//! (`const_pattern_desugar.rs`) collected const/static names from the WHOLE
//! tree, DELIBERATELY — its own header records four cardinal false verifies
//! that came from enumerating container shapes instead. But in real Rust a
//! `const` declared in another function's body is NOT in scope, so a bare arm
//! pattern of that name is a BINDER. Treating it as a const-pattern marker is
//! fail-closed for the arm-reachability lane and NOT fail-closed for the
//! ghost-closure lane: the arm body's `v` then resolves to the PARAMETER
//! `v: Seq<u64>`, the parameter is ghost, the closure is skipped, and a body
//! that ALWAYS divides by zero comes back `Verified`. `InScopeDecls` points
//! the same whole-subtree scan at the scopes that CONTAIN the target function
//! instead of at the whole file.
//!
//! THE DEFECT, HALF TWO (the ghost-closure lane, fixed on `work/wCLO`). An
//! ESCAPING closure's body was never checked at all, so BOTH fixtures below
//! verified and the name difference was invisible. That is why the `work/wCONST`
//! copy of this file had to DROP the fail-closed assertion on the control and
//! declare itself vacuous: on a tree with the scope fix and without the closure
//! fixes, the two files agree at `Verified`, and the agreement assertion passes
//! for the wrong reason.
//!
//! WHAT IS PINNED HERE, post-merge, is both halves at once:
//!
//!   (1) the CONTROL fails closed — `zc_shadow_cx` divides by zero in an
//!       escaping closure, so it must not verify, with no const in scope to
//!       explain anything away; this is the half `work/wCONST` could not assert;
//!   (2) the two files AGREE — their only difference is the NAME of a `const`
//!       declared inside a DIFFERENT function's body, which Rust does not have
//!       in scope here, so it must not decide this verdict; this is the half
//!       `work/wCLO` could not assert, and its copy asserted the opposite as a
//!       residual ratchet.
//!
//! Neither assertion subsumes the other: (1) alone passed on `work/wCLO` while
//! the name still moved the verdict, and (2) alone passed on `main` while both
//! sides were false verifies. Together they are the fact.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verdict(file: &str, func: &str) -> VerifyResult {
    let path = format!("{}/tests/data/{file}", env!("CARGO_MANIFEST_DIR"));
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&path, func)
    })
    .unwrap_or_else(|e| panic!("extract+verify `{func}` in `{file}` failed: {e:?}"))
}

#[test]
fn zc1_a_body_const_in_another_function_no_longer_changes_this_verdict() {
    let contaminated = verdict("const_scope_contamination_repro.rs", "zc_shadow_cx");
    let control = verdict("const_scope_contamination_control_repro.rs", "zc_shadow_cx");

    // (1) THE CONTROL MUST FAIL CLOSED. `zc_shadow_cx` always divides by zero
    // inside an escaping closure; a `Verified` here is a FALSE VERIFY whatever
    // the scope model says.
    assert!(
        !matches!(control, VerifyResult::Verified),
        "CONTROL WENT UNSOUND: `zc_shadow_cx` divides by zero in an escaping \
         closure and there is no const of that name anywhere in scope; it must \
         not verify. Got {control:?}"
    );

    // (2) AND THE CONTAMINATED FILE MUST AGREE WITH IT.
    assert_eq!(
        std::mem::discriminant(&contaminated),
        std::mem::discriminant(&control),
        "SCOPE CONTAMINATION IS BACK: the only difference between these two \
         files is the NAME of a `const` declared inside a DIFFERENT function's \
         body, which Rust does not have in scope here, so it must not decide \
         this verdict; got {contaminated:?} vs {control:?}"
    );
}
