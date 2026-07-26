// Trait DEFAULT bodies are conformance-checked through an EMPTY impl
// (soundness regression guard).
//
// WHY THIS EXISTS. `impl Tr for bool {}` is an empty impl: it supplies NO
// method body, so the conformance pass has nothing of its own to capture — the
// method it inherits lives on the `TraitDecl`. Meanwhile the caller-side
// contract axiom IS emitted from that same `TraitDecl`, and a generic caller
// consumes it (see `default_body_satisfying_contract_lets_caller_verify` — the
// axiom demonstrably reaches the caller).
//
// That is a false-verify shape on its face: if nothing checks the DEFAULT body
// against the contract, a caller assumes a postcondition NOBODY discharged. The
// existing `trait_conformance_body_shapes.rs` guard does not cover it — every
// case there has an explicit impl body.
//
// These cases pin that the default body IS checked. `contract_violating_default_
// body_is_refuted_through_empty_impl` is the cardinal one: the default body
// returns `false` while the contract promises `returns(true)`, so at RUNTIME the
// call yields false and `assert!(returned)` is FALSE. If it ever VERIFIES we are
// proving a false statement about a real execution — a cardinal soundness
// failure, not a completeness loss.
//
// Upstream shape: returns_postcondition.rs::default_trait_fn_with_returns{,2}.
//
// NOTE (attribution): a conformance failure is an obligation of the IMPL, not of
// whatever function shares the file, so the violating default is refuted on its
// OWN obligation (`conformance_verdict`) while the caller — which assumes the
// declared contract, exactly as in Verus — verifies. The FILE still fails. Each
// shape keeps its own source string so the satisfying and violating cases stay
// independently observable. See
// the internal conformance-attribution design note.

use trust_vc_core::{verify_function_from_file, VerifyResult};

/// Default body SATISFIES `returns(true)`. The caller must VERIFY — this is the
/// control that proves the contract axiom actually reaches the caller. Without
/// it, the cardinal case below could "pass" for the vacuous reason that no axiom
/// is emitted at all.
const SATISFYING_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
trait Tr: Sized {
    #[trust_vc::returns(true)]
    fn m(self) -> bool {
        true
    }
}

#[trust_vc::trait_impl]
impl Tr for bool {}

#[trust_vc::ensures(true)]
fn caller<T: Tr>(value: T) {
    let returned = value.m();
    trust_vc::assert!(returned);
}

#[trust_vc::ensures(true)]
fn caller_then_false<T: Tr>(value: T) {
    let returned = value.m();
    trust_vc::assert!(returned);
    trust_vc::assert!(false);
}
"#;

/// Byte-identical to `SATISFYING_DEFAULT` except the default body returns
/// `false`, violating its own `returns(true)`. The empty impl inherits it.
const VIOLATING_DEFAULT: &str = r#"
#[trust_vc::trait_spec]
trait Tr: Sized {
    #[trust_vc::returns(true)]
    fn m(self) -> bool {
        false
    }
}

#[trust_vc::trait_impl]
impl Tr for bool {}

#[trust_vc::ensures(true)]
fn caller<T: Tr>(value: T) {
    let returned = value.m();
    trust_vc::assert!(returned);
}
"#;

/// Unique path per fixture. Cases here share the function name `caller` across
/// DIFFERENT sources, so a name-keyed path would let parallel tests race on one
/// file and read it back truncated (see the same fix in
/// `trait_conformance_body_shapes.rs`).
fn verify(src: &str, case: &str) -> VerifyResult {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);

    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_default_body_conf_{}_{}_{case}.rs",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, src).expect("write fixture");
    let r = verify_function_from_file(path.to_str().unwrap(), case).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&path);
    r
}

/// The file's CONFORMANCE verdict — the channel through which `cargo trust-vc
/// check` reports an impl.
///
/// ATTRIBUTION (per the internal conformance-attribution design note): a
/// conformance failure is an obligation of the IMPL, not of whatever function
/// happens to share the file. Folding it into every function's verdict made
/// upstream trait files structurally unportable — upstream
/// `returns_postcondition.rs::trait_returns_on_trait_method_decl` pins a GENERIC
/// caller `test_call<T: Tr>` VERIFYING while impls Y/Z/W of that same trait FAIL.
/// Every impl is still CHECKED, always; only the BLAME moved, so a guard asking
/// "was the violating body CAUGHT?" asks the impl's own obligation. It
/// ENUMERATES every conformance obligation of the file and verifies each BY NAME,
/// returning the first non-`Verified` result. The file still FAILS.
fn conformance_verdict(src: &str, case: &str) -> VerifyResult {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);

    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_default_body_conf_conf_{}_{}_{case}.rs",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, src).expect("write fixture");
    let r = conformance_verdict_for_path(path.to_str().unwrap());
    let _ = std::fs::remove_file(&path);
    r
}

/// Enumerate + verify-by-name, exactly as `cargo trust-vc check` drives it.
fn conformance_verdict_for_path(path: &str) -> VerifyResult {
    let names = match trust_vc_core::list_trait_conformance_obligations(path) {
        Ok(names) => names,
        Err(err) => {
            return VerifyResult::Error {
                message: err.to_string(),
            }
        }
    };
    for name in names {
        match trust_vc_core::verify_trait_conformance_obligation(path, &name) {
            Ok(result) if result.is_verified() => {}
            Ok(result) => return result,
            Err(err) => {
                return VerifyResult::Error {
                    message: err.to_string(),
                }
            }
        }
    }
    VerifyResult::Verified
}

/// The contract axiom from a trait DEFAULT method reaches a generic caller
/// through an empty impl. Load-bearing: it is what makes the cardinal case below
/// meaningful rather than vacuous.
#[test]
fn default_body_satisfying_contract_lets_caller_verify() {
    match verify(SATISFYING_DEFAULT, "caller") {
        VerifyResult::Verified => {}
        other => panic!(
            "expected VERIFIED: a default body that SATISFIES `returns(true)` must let a \
             generic caller assume it. Got {other:?}. If this regressed to a counterexample \
             the contract axiom no longer reaches callers — which would silently make \
             `contract_violating_default_body_is_refuted_through_empty_impl` VACUOUS."
        ),
    }
}

/// The inherited-default axiom set is CONSISTENT: it must not prove `false`.
/// This is upstream `default_trait_fn_with_returns::test3`, which Verus reports
/// as exactly one failure.
#[test]
fn default_body_axiom_does_not_prove_false() {
    match verify(SATISFYING_DEFAULT, "caller_then_false") {
        VerifyResult::Counterexample { .. } => {}
        VerifyResult::Verified => panic!(
            "CARDINAL: `assert!(false)` VERIFIED after calling a default trait method. \
             The inherited-contract axiom set is INCONSISTENT — it proves anything."
        ),
        other => panic!("expected a counterexample on `assert!(false)`, got {other:?}"),
    }
}

/// THE CARDINAL CASE. The default body returns `false` but its contract promises
/// `returns(true)`, and the impl is EMPTY so there is no impl-method body to
/// capture. At runtime the call yields `false`, so the caller's
/// `assert!(returned)` is FALSE.
#[test]
fn contract_violating_default_body_is_refuted_through_empty_impl() {
    match conformance_verdict(VIOLATING_DEFAULT, "caller") {
        VerifyResult::Counterexample {
            ref obligation_name,
            ..
        } if obligation_name.contains("trait impl conformance") => {}
        VerifyResult::Verified => panic!(
            "CARDINAL FALSE-VERIFY — a trait DEFAULT body that violates its own \
             `returns` contract DISCHARGED its conformance obligation, because the impl is \
             empty and the conformance pass had no impl-method body to capture. Callers \
             assume a postcondition that is FALSE at runtime, and the file is certified \
             where Verus errors."
        ),
        other => panic!(
            "expected a `trait impl conformance` counterexample (proving the default body \
             was actually checked), got {other:?}. An Error here would mean the call stopped \
             resolving rather than the contract being checked, hollowing out this guard."
        ),
    }
}
