// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Faithful TrustVc port of upstream rust_verify_test/tests/assert_forall_by.rs
// (pinned ref a40d57c73650cd3648b09386bfdb96ab5c270626), which has 17 cases.
//
// Every `case_id` below is a real TrustVc function in this file, and every
// `upstream_case_id` is a real upstream `#[test]` name. An upstream case built
// from several fns is ported as several TrustVc fns SHARING that upstream case
// id (the convention the accepted multiset.rs / z3_restart.rs ports use).
//
// The file is NOT compiled — it is syn-parsed and verified through
// `verify_function_from_file`, so it carries the Verus-shaped surface directly.
//
//   upstream case              upstream outcome                   TrustVc fn(s)
//   -------------------------  ---------------------------------  -------------------------------------
//   test_assertby1             Ok(())                             assertby_test
//   test_assertby1_fail1       assert_one_fails                   assertby_test_fail1
//   test_assertby1_fail2       assert_one_fails                   assertby_test_fail2
//   test_assertby1_fail3       vir error, mode spec vs proof      assertby_proof_var_disallowed
//   test_forallstmt1           Ok(())                             forallstmt_test,
//                                                                 forallstmt_test_inference,
//                                                                 forallstmt_proof_var_allowed_as_spec
//   test_forallstmt1_fail1     assert_one_fails                   forallstmt_test_fail1
//   test_forallstmt1_fail2     assert_one_fails                   forallstmt_test_fail2
//   test_forallstmt1_fail3     vir error, mode spec vs proof      forallstmt_proof_var_disallowed
//   test_forallstmt2           Ok(())                             forallstmt2_test
//   test_forallstmt2_fails1    assert_one_fails                   forallstmt2_test_fails1
//   test_forallstmt2_fails2    assert_one_fails                   forallstmt2_test_fails2
//   test_scope                 Ok(())                             scope
//   test_forallstmt_typ        Ok(())                             forallstmt_typ
//   test_forallstmt_typ_fails  assert_one_fails                   forallstmt_typ_fails
//   test_assertby1_let         Ok(())                             assertby_let
//   test_forallstmt_let        Ok(())                             forallstmt_let
//   test_forallstmt_implies    Ok(err) + warning                  forallstmt_implies
//
// ---------------------------------------------------------------------------
// SURFACE NOTES (TrustVc spellings of the Verus constructs)
//
//  * Upstream's fns carry no postcondition. Each TrustVc CASE fn carries
//    `#[trust_vc::ensures(true)]` so `cargo trust-vc`'s scanner discovers it and
//    its body obligations are scheduled — the same convention the accepted
//    z3_restart.rs / inline.rs ports use. `ensures(true)` is trivially true and
//    adds no proof strength.
//
//  * `tracked x: bool` is Verus's proof-mode parameter. In the `verus!` surface
//    it desugars to exactly `#[verifier::proof] x: bool` (rust_to_vir_func.rs
//    `get_var_mode` reads the mode off that attribute), which is why upstream
//    uses BOTH spellings in this file. TrustVc accepts `tracked p` verbatim and
//    spells the attribute form `#[trust_vc::proof] p`.
//
//  * `consume` / `no_consume` are upstream's SIGNATURE-ONLY proof helpers (empty
//    body, no contract): they exist purely so a by-block has something to call.
//    They carry no proof obligation and are not upstream cases.
//
//  * `A implies B` (the Verus KEYWORD) and `A ==> B` are DIFFERENT constructs
//    and this port keeps upstream's choice verbatim for each case. Both prove
//    the same goal `forall x. A ==> B`, but the `implies` by-block may ASSUME
//    `A` while the `==>` by-block may not — and `==>` therefore raises Verus's
//    warning "using ==> in `assert forall` does not currently assume the
//    antecedent in the body". Measured against the pinned Verus build (real z3):
//    the `implies` form of test_forallstmt2 emits ZERO warnings; the `==>` form
//    of test_forallstmt_implies emits that one warning. Rendering upstream's
//    `implies` cases with `==>` would therefore emit a warning upstream does not,
//    and upstream's default `=> Ok(())` harness arm asserts `warnings.len() == 0`.
//
//  * upstream `test_forallstmt_implies` asserts TWO warnings. Measured on the
//    pinned build, the second is rustc's own emitter summary line
//    `1 warning emitted` (a `warning`-level rustc diagnostic that the upstream
//    harness's `parse_diags` scoops into `err.warnings`), not a verifier warning
//    — which is why upstream content-checks only the first. TrustVc reproduces
//    the one VERIFIER warning; it has no rustc emitter to produce a summary line.
//
//  * `uninterp spec fn f(x: int) -> bool;` (a spec fn DECLARED with no body) is
//    written verbatim: a bodyless `#[trust_vc::spec]` fn is declared as a symbol
//    and never given a defining axiom, and no `reveal!` can conjure one because
//    there is no body to reveal. Pinned by
//    `trust-vc-core/tests/uninterp_spec_fn.rs` (neither `p(3)` nor `!p(3)` is
//    provable) and, for this file, by
//    `assert_forall_by_rs_implies_hypothesis_is_load_bearing`.
// ---------------------------------------------------------------------------

use trust_vc_types::{int, nat};

// (case_id, upstream_case_id, expected_verdict, min_obligations)
//
// `min_obligations` is the count the CORPUS records, and it is auto-pinned from a
// genuine `--refresh-trust-vc-corpus-evidence --run-trust-vc-corpus` run — the
// manifest's `min_obligations` and `obligation_fingerprints` must agree with these
// (pinned by `assert_forall_by_rs_expected_case_metadata_matches_manifest`). Two
// things make it differ from a naive count of the asserts in the body:
//
//   * it counts DISTINCT obligations. `assertby_test` schedules three (the
//     by-block's conclusion, the trailing `assert`, and `ensures(true)`) but the
//     first two are the SAME formula `f1(3) > 3`, so it records two.
//   * for a counterexample case it stops at the FAILING obligation. The three
//     cases that fail on their very first obligation (`assertby_test_fail1`,
//     `forallstmt_test_fail1`, `forallstmt2_test_fails2`, `forallstmt_typ_fails`)
//     therefore record exactly one.
pub const ASSERT_FORALL_BY_RS_EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    // ---- test_assertby1 family ----
    ("assertby_test", "test_assertby1", "verified", 2),
    (
        "assertby_test_fail1",
        "test_assertby1_fail1",
        "counterexample",
        1,
    ),
    (
        "assertby_test_fail2",
        "test_assertby1_fail2",
        "counterexample",
        3,
    ),
    (
        "assertby_proof_var_disallowed",
        "test_assertby1_fail3",
        "error",
        0,
    ),
    // ---- test_forallstmt1 family ----
    ("forallstmt_test", "test_forallstmt1", "verified", 3),
    (
        "forallstmt_test_inference",
        "test_forallstmt1",
        "verified",
        3,
    ),
    (
        "forallstmt_proof_var_allowed_as_spec",
        "test_forallstmt1",
        "verified",
        2,
    ),
    (
        "forallstmt_test_fail1",
        "test_forallstmt1_fail1",
        "counterexample",
        1,
    ),
    (
        "forallstmt_test_fail2",
        "test_forallstmt1_fail2",
        "counterexample",
        3,
    ),
    (
        "forallstmt_proof_var_disallowed",
        "test_forallstmt1_fail3",
        "error",
        0,
    ),
    // ---- test_forallstmt2 family (the `implies` KEYWORD) ----
    ("forallstmt2_test", "test_forallstmt2", "verified", 3),
    (
        "forallstmt2_test_fails1",
        "test_forallstmt2_fails1",
        "counterexample",
        3,
    ),
    (
        "forallstmt2_test_fails2",
        "test_forallstmt2_fails2",
        "counterexample",
        1,
    ),
    // ---- scope / typing / let ----
    ("scope", "test_scope", "verified", 3),
    ("forallstmt_typ", "test_forallstmt_typ", "verified", 3),
    (
        "forallstmt_typ_fails",
        "test_forallstmt_typ_fails",
        "counterexample",
        1,
    ),
    ("assertby_let", "test_assertby1_let", "verified", 3),
    ("forallstmt_let", "test_forallstmt_let", "verified", 3),
    // ---- `==>` (warns) ----
    (
        "forallstmt_implies",
        "test_forallstmt_implies",
        "verified",
        1,
    ),
];

pub fn assert_forall_by_rs_expected_cases(
) -> &'static [(&'static str, &'static str, &'static str, usize)] {
    ASSERT_FORALL_BY_RS_EXPECTED_CASES
}

/// The one verifier warning upstream `test_forallstmt_implies` content-checks.
pub const ASSERT_FORALL_BY_RS_IMPLIES_WARNING: &str =
    "using ==> in `assert forall` does not currently assume the antecedent in the body";

// upstream: #[verifier(opaque)] spec fn f1(i: int) -> int { i + 1 }
#[trust_vc::spec]
#[trust_vc::opaque]
fn f1(i: int) -> int {
    i + 1
}

// upstream signature-only proof helpers (empty body, no contract):
//   proof fn consume(tracked x: bool) { }     — a PROOF-mode parameter
//   proof fn no_consume(x: bool) { }          — a SPEC-mode parameter (a proof
//                                               fn's params default to spec)
#[trust_vc::proof]
fn consume(tracked x: bool) {}

#[trust_vc::proof]
fn no_consume(x: bool) {}

// ===========================================================================
// test_assertby1 => Ok(())
//
//   assert(f1(3) > 3) by { reveal(f1); }
//   assert(f1(3) > 3);
//
// The by-block's `reveal` is SCOPED to the block, but the CONCLUSION it proves
// persists as a fact — so the trailing assert still holds with f1 opaque again.
// ===========================================================================
#[trust_vc::ensures(true)]
fn assertby_test() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) > 3int);
}

// ===========================================================================
// test_assertby1_fail1 => assert_one_fails
//
//   assert(f1(3) > 4) by { reveal(f1); }   // FAILS
// ===========================================================================
#[trust_vc::ensures(true)]
fn assertby_test_fail1() {
    trust_vc::assert_by!(f1(3int) > 4int, { // FAILS
        trust_vc::reveal!(f1);
    });
}

// ===========================================================================
// test_assertby1_fail2 => assert_one_fails
//
//   assert(f1(3) > 3) by { reveal(f1); }
//   assert(f1(3) == 4);                    // FAILS
//
// THE SCOPED-REVEAL PIN: `f1(3) == 4` is provable ONLY from f1's body, which is
// opaque again outside the block. A reveal that leaked past the block would
// prove MORE than Verus.
// ===========================================================================
#[trust_vc::ensures(true)]
fn assertby_test_fail2() {
    trust_vc::assert_by!(f1(3int) > 3int, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) == 4int); // FAILS
}

// ===========================================================================
// test_assertby1_fail3 => assert_vir_error_msg(
//                             "expression has mode spec, expected mode proof")
//
//   proof fn consume(tracked x: bool) { }
//   proof fn assertby_proof_var_disallowed(tracked x: bool) {
//       assert(true) by { consume(x) }
//   }
//
// Verus pushes `in_forall_stmt` for BOTH assert-by flavours (vir/src/modes.rs,
// `ExprX::AssertBy` — its REVIEW comment is explicitly about the vars.len() == 0
// case), so inside the block a PROOF-mode variable READS at mode `spec`. Passing
// it to `consume`'s `tracked` (proof-mode) parameter is therefore a mode error.
// ===========================================================================
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn assertby_proof_var_disallowed(tracked x: bool) {
    trust_vc::assert_by!(true, {
        consume(x);
    });
}

// ===========================================================================
// test_forallstmt1 => Ok(())   [3 fns]
//
//   fn forallstmt_test() {
//       assert forall|x: int| f1(x) > x by { reveal(f1); }
//       assert(f1(3) > 3);
//   }
//   fn forallstmt_test_inference() {
//       assert forall|x| f1(x) > x by { reveal(f1); }   // binder type INFERRED
//       assert(f1(3) > 3);
//   }
//   fn forallstmt_proof_var_allowed_as_spec(#[verifier::proof] x: bool) {
//       assert forall|i: int| f1(i) == f1(i) by { no_consume(x); }
//   }
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt_test() {
    trust_vc::assert_forall_by!(|x: int| f1(x) > x, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) > 3int);
}

// The binder carries NO type annotation: it is inferred from `f1`'s declared
// parameter type, exactly as upstream's inference variant requires.
#[trust_vc::ensures(true)]
fn forallstmt_test_inference() {
    trust_vc::assert_forall_by!(|x| f1(x) > x, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) > 3int);
}

// The POSITIVE counterpart of the two fail3 cases: a proof-mode variable that is
// DEMOTED to spec inside the by-block may still be used where SPEC mode is
// expected — `no_consume`'s parameter is spec-mode (a proof fn's parameters
// default to spec). This must VERIFY.
#[trust_vc::ensures(true)]
fn forallstmt_proof_var_allowed_as_spec(#[trust_vc::proof] x: bool) {
    trust_vc::assert_forall_by!(|i: int| f1(i) == f1(i), {
        no_consume(x);
    });
}

// ===========================================================================
// test_forallstmt1_fail1 => assert_one_fails
//
//   assert forall|x: int| f1(x) < x by { reveal(f1); }   // FAILS
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt_test_fail1() {
    trust_vc::assert_forall_by!(|x: int| f1(x) < x, { // FAILS
        trust_vc::reveal!(f1);
    });
}

// ===========================================================================
// test_forallstmt1_fail2 => assert_one_fails
//
//   assert forall|x: int| f1(x) > x by { reveal(f1); }
//   assert(f1(3) == 4);                                  // FAILS
//
// The quantified-flavour scoped-reveal pin. Outside the block the only fact is
// `forall x. f1(x) > x`, which does NOT entail `f1(3) == 4` (f1 = λx. x+2 is a
// model of the hypothesis with f1(3) == 5). TrustVc fails closed on this
// obligation with a model-less solver-incompleteness Unknown, which maps to the
// gate's `counterexample` class (= upstream `assert_one_fails`, which never
// inspects a model) exactly as docs/design-unknown-as-failure.md prescribes and
// as the accepted z3_restart.rs port's `test1_fails` does. The obligation being
// a GENUINE non-proof — not a faithfulness gap — is pinned constructively by
// `assert_forall_by_rs_fail2_obligation_is_genuinely_unprovable`.
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt_test_fail2() {
    trust_vc::assert_forall_by!(|x: int| f1(x) > x, {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) == 4int); // FAILS
}

// ===========================================================================
// test_forallstmt1_fail3 => assert_vir_error_msg(
//                               "expression has mode spec, expected mode proof")
//
//   proof fn forallstmt_proof_var_disallowed(tracked x: bool) {
//       assert forall|i: int| f1(i) == f1(i) by { consume(x); }
//   }
// ===========================================================================
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn forallstmt_proof_var_disallowed(tracked x: bool) {
    trust_vc::assert_forall_by!(|i: int| f1(i) == f1(i), {
        consume(x);
    });
}

// ===========================================================================
// test_forallstmt2 => Ok(())   [ZERO warnings]
//
//   assert forall|x: int| 0 <= x implies 1 <= f1(x) by { reveal(f1); }
//   assert(f1(3) > 0);
//
// The `implies` KEYWORD: the by-block may ASSUME `0 <= x`, and no warning fires.
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt2_test() {
    trust_vc::assert_forall_by!(assert forall|x: int| 0int <= x implies 1int <= f1(x) by {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) > 0int);
}

// ===========================================================================
// test_forallstmt2_fails1 => assert_one_fails
//
//   assert forall|x: int| 0 <= x implies 1 <= f1(x) by { reveal(f1); }
//   assert(f1(-3) > 0);                                  // FAILS
//
// The quantified fact is GUARDED by `0 <= x`, so it says nothing at x == -3.
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt2_test_fails1() {
    trust_vc::assert_forall_by!(assert forall|x: int| 0int <= x implies 1int <= f1(x) by {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(-3int) > 0int); // FAILS
}

// ===========================================================================
// test_forallstmt2_fails2 => assert_one_fails
//
//   assert forall|x: int| 1 <= f1(x) by { reveal(f1); }  // FAILS (unguarded)
//   assert(f1(3) > 0);
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt2_test_fails2() {
    trust_vc::assert_forall_by!(|x: int| 1int <= f1(x), { // FAILS
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) > 0int);
}

// ===========================================================================
// test_scope => Ok(())
//
//   spec fn f(j: int) -> bool { true }
//   fn scope(b: bool, i: u64) {
//       if b { let i = 5; assert forall|i: int| f(i) by {}
//                         assert forall|j: int| f(j) by {} }
//       else { let i = 6; ... }
//   }
//
// The `assert forall` binder `i` SHADOWS both the `i: u64` parameter and the
// `let i` local. TrustVc alpha-renames a colliding binder to a fresh solver
// symbol; the binder is a genuine fresh `int`, never the outer `u64`.
// ===========================================================================
#[trust_vc::spec]
fn f(j: int) -> bool {
    true
}

#[trust_vc::ensures(true)]
fn scope(b: bool, i: u64) {
    if b {
        let i = 5;
        trust_vc::assert_forall_by!(|i: int| f(i), {});
        trust_vc::assert_forall_by!(|j: int| f(j), {});
    } else {
        let i = 6;
        trust_vc::assert_forall_by!(|i: int| f(i), {});
        trust_vc::assert_forall_by!(|j: int| f(j), {});
    }
}

// ===========================================================================
// test_forallstmt_typ => Ok(())
//
//   assert forall|x: nat| 1 <= f1(x as int) by { reveal(f1); }
//   assert(f1(3) > 0);
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt_typ() {
    trust_vc::assert_forall_by!(|x: nat| 1int <= f1(x as int), {
        trust_vc::reveal!(f1);
    });
    trust_vc::assert!(f1(3int) > 0int);
}

// ===========================================================================
// test_forallstmt_typ_fails => assert_one_fails
//
//   assert forall|x: nat| 1 <= f1(x as int) by {}        // FAILS (no reveal)
//   assert(f1(3) > 0);
//
// The by-block is EMPTY, so f1 stays opaque and the bound is not provable.
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt_typ_fails() {
    trust_vc::assert_forall_by!(|x: nat| 1int <= f1(x as int), {}); // FAILS
    trust_vc::assert!(f1(3int) > 0int);
}

// ===========================================================================
// test_assertby1_let => Ok(())
//
//   assert({let a = 3; f1(a) > a}) by { reveal(f1); }
//   assert(f1(3) > 3);
// ===========================================================================
#[trust_vc::ensures(true)]
fn assertby_let() {
    trust_vc::assert_by!(
        {
            let a: int = 3int;
            f1(a) > a
        },
        {
            trust_vc::reveal!(f1);
        }
    );
    trust_vc::assert!(f1(3int) > 3int);
}

// ===========================================================================
// test_forallstmt_let => Ok(())
//
//   assert forall|x: nat| { let a: int = 1; a <= #[trigger] f1(x as int) } by {
//       reveal(f1);
//   }
//   assert(f1(3) > 0);
// ===========================================================================
#[trust_vc::ensures(true)]
fn forallstmt_let() {
    trust_vc::assert_forall_by!(
        |x: nat| {
            let a: int = 1int;
            a <= #[trigger] f1(x as int)
        },
        {
            trust_vc::reveal!(f1);
        }
    );
    trust_vc::assert!(f1(3int) > 0int);
}

// ===========================================================================
// test_forallstmt_implies => Ok(err), errors empty, ONE verifier warning
//
//   uninterp spec fn f(x: int) -> bool;
//   uninterp spec fn g(x: int) -> bool;
//   proof fn x()
//       requires forall |x: int| f(x) ==> g(x)
//   { assert forall |x: int| f(x) ==> g(x) by { } }
//
// `==>` (not `implies`): the by-block does NOT assume the antecedent, which is
// exactly what the warning says — pinned by
// `assert_forall_by_rs_implies_does_not_assume_the_antecedent`.
//
// `uninterp spec fn` — a spec function DECLARED with no body — is upstream's own
// surface, and it is trust-vc's too: a bodyless `#[trust_vc::spec]` fn is
// declared as a symbol and NEVER given a defining axiom (no `reveal!` can conjure
// one, because there is no body to reveal). Pinned by
// `trust-vc-core/tests/uninterp_spec_fn.rs`.
//
// They are named `implies_f` / `implies_g` rather than upstream's `f` / `g`
// because a port file merges ALL of an upstream file's cases into ONE file, and
// `test_scope` already defines a `spec fn f(j: int) -> bool`.
// ===========================================================================
#[trust_vc::spec]
fn implies_f(x: int) -> bool;

#[trust_vc::spec]
fn implies_g(x: int) -> bool;

#[trust_vc::proof]
#[trust_vc::requires(forall|x: int| implies_f(x) ==> implies_g(x))]
fn forallstmt_implies() {
    trust_vc::assert_forall_by!(|x: int| implies_f(x) ==> implies_g(x), {});
}
