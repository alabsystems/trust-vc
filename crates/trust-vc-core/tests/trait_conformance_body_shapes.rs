// Trait-impl conformance is BODY-SHAPE ROBUST (soundness regression guard).
//
// WHY THIS EXISTS. The caller-side trait contract axiom (Slice 1/1b of #33) is
// sound ONLY because the conformance pass proves `body ⊨ contract` for every
// impl. That pass is driven by `capture_conformance_method_body`, whose gate is
// "a single pure return" — and `trait_conformance.rs` SKIPS the check
// (`continue`) for any body it fails to capture, while the trait's postcondition
// axiom is still emitted from the `TraitDecl` regardless. On its face that is a
// false-verify shape: an impl whose body VIOLATES the contract but whose body
// SHAPE evades capture would leave a concrete caller assuming a contract nobody
// proved.
//
// These cases pin that this does NOT happen. Each impl below violates
// `ensures(result >= 10)` by returning 0, through a body shape that is NOT a
// bare literal return — `let`-bound, helper-call, block-wrapped, and `if`/`else`.
// Every one must be caught by the conformance obligation
// ("trait impl conformance Contracted::get for Widget"), which is the IMPL's own
// addressable case — where a conformance failure is now attributed (the caller
// assumes the declared contract, exactly as in Verus; the FILE still fails
// because the impl's obligation is refuted). See
// the internal conformance-attribution design note.
//
// A regression here (any case flipping to Verified) is a CARDINAL soundness
// failure — we would be proving something Verus rejects — not a mere
// completeness loss. Do not relax these to `expect_fail_closed`: an `Error` is
// NOT an acceptable outcome either, because it would mean the call stopped
// resolving rather than the contract being checked.

use trust_vc_core::VerifyResult;

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
///
/// Each fixture uses a unique path. Every case names its function `caller`, so
/// sharing a case-keyed path let parallel test threads overwrite or delete one
/// another's fixture and occasionally produced a parse `Error` instead of a
/// real conformance verdict. The process-local counter keeps those paths
/// disjoint, making this soundness guard deterministic under the test harness.
fn conformance_verdict(src: &str, case: &str) -> VerifyResult {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);

    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_conf_shape_conf_{}_{}_{case}.rs",
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

/// Asserts the conformance obligation REFUTED the violating impl.
///
/// Stricter than `!Verified` on purpose: an `Error` would mean the call stopped
/// RESOLVING (so the contract was never even consumed), which would silently
/// hollow out this guard — the test would "pass" while testing nothing. Only a
/// genuine conformance counterexample proves the check actually ran.
fn assert_conformance_refuted(label: &str, r: VerifyResult) {
    match r {
        VerifyResult::Counterexample {
            ref obligation_name,
            ..
        } if obligation_name.contains("trait impl conformance") => {}
        VerifyResult::Verified => panic!(
            "{label}: CARDINAL FALSE-VERIFY — a contract-violating impl DISCHARGED its own \
             conformance obligation. The conformance pass did not fire for this body shape, so \
             callers assume a contract nobody proved and the file is certified where Verus \
             errors."
        ),
        other => panic!(
            "{label}: expected a `trait impl conformance` counterexample (proving the \
             check ran), got {other:?}. An Error here means the call stopped resolving, \
             which would hollow out this soundness guard."
        ),
    }
}

// CONTROL: capturable violating body `{ 0 }` under `ensures(result >= 10)`.
// Known-good: conformance catches this -> caller must NOT verify.
const CONTROL_CAPTURABLE: &str = r#"
#[trust_vc::trait_spec]
trait Contracted { #[trust_vc::ensures(result >= 10)] fn get(&self) -> i32; }
struct Widget(i32);
#[trust_vc::trait_impl]
impl Contracted for Widget { fn get(&self) -> i32 { 0 } }
#[trust_vc::ensures(true)]
fn caller(w: Widget) { let r = w.get(); trust_vc::assert!(r >= 10); }
"#;

#[test]
fn control_capturable_violating_body_is_caught() {
    let r = conformance_verdict(CONTROL_CAPTURABLE, "caller");
    assert_conformance_refuted("control (literal body)", r);
}

// CASE A: violating body behind a `let` statement (not a single pure return).
const PROBE_LET: &str = r#"
#[trust_vc::trait_spec]
trait Contracted { #[trust_vc::ensures(result >= 10)] fn get(&self) -> i32; }
struct Widget(i32);
#[trust_vc::trait_impl]
impl Contracted for Widget { fn get(&self) -> i32 { let x = 0; x } }
#[trust_vc::ensures(true)]
fn caller(w: Widget) { let r = w.get(); trust_vc::assert!(r >= 10); }
"#;

#[test]
fn let_bound_violating_body_is_caught() {
    let r = conformance_verdict(PROBE_LET, "caller");
    assert_conformance_refuted("let-bound body", r);
}

// CASE B: violating body via a helper call (not a pure literal return).
const PROBE_CALL: &str = r#"
#[trust_vc::spec]
fn zero() -> i32 { 0 }
#[trust_vc::trait_spec]
trait Contracted { #[trust_vc::ensures(result >= 10)] fn get(&self) -> i32; }
struct Widget(i32);
#[trust_vc::trait_impl]
impl Contracted for Widget { fn get(&self) -> i32 { zero() } }
#[trust_vc::ensures(true)]
fn caller(w: Widget) { let r = w.get(); trust_vc::assert!(r >= 10); }
"#;

#[test]
fn call_returning_violating_body_is_caught() {
    let r = conformance_verdict(PROBE_CALL, "caller");
    assert_conformance_refuted("call-returning body", r);
}

// CASE C: violating body wrapped in a nested block expression.
const PROBE_BLOCK: &str = r#"
#[trust_vc::trait_spec]
trait Contracted { #[trust_vc::ensures(result >= 10)] fn get(&self) -> i32; }
struct Widget(i32);
#[trust_vc::trait_impl]
impl Contracted for Widget { fn get(&self) -> i32 { { 0 } } }
#[trust_vc::ensures(true)]
fn caller(w: Widget) { let r = w.get(); trust_vc::assert!(r >= 10); }
"#;

#[test]
fn block_wrapped_violating_body_is_caught() {
    let r = conformance_verdict(PROBE_BLOCK, "caller");
    assert_conformance_refuted("block-wrapped body", r);
}

// CASE D: the sharpest form — an `if/else` body that violates on one branch.
const PROBE_IF: &str = r#"
#[trust_vc::trait_spec]
trait Contracted { #[trust_vc::ensures(result >= 10)] fn get(&self) -> i32; }
struct Widget(i32);
#[trust_vc::trait_impl]
impl Contracted for Widget { fn get(&self) -> i32 { if self.0 > 0 { 0 } else { 0 } } }
#[trust_vc::ensures(true)]
fn caller(w: Widget) { let r = w.get(); trust_vc::assert!(r >= 10); }
"#;

#[test]
fn if_else_violating_body_is_caught() {
    let r = conformance_verdict(PROBE_IF, "caller");
    assert_conformance_refuted("if-else body", r);
}
