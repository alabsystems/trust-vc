// Slice 1 of #33: concrete-impl trait-method VALUE resolution.
//
// A spec-context call on a CONCRETE receiver (`s.g()` where `impl Tr for S`)
// now resolves to the trait UF `Tr__g` with the receiver lifted into the trait
// UF's `Poly` self-domain via the impl's `Box_S` bridge, so the value is
// supplied by the trait's declared postcondition axiom (contract) — exactly as
// the generic path already did. Previously this hard-errored ("method not
// available in specification context").
//
// These tests PIN the soundness envelope: the value comes ONLY from the trait
// CONTRACT, never the impl body (that is Slice 2, not implemented); a
// contract-VIOLATING impl cannot let a caller assume the false contract
// (conformance gates the call-site axiom); and distinct impls never cross-leak.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(src: &str, case: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_concrete_trait_{}_{case}.rs",
        std::process::id()
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
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_concrete_trait_conf_{}_{case}.rs",
        std::process::id()
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

// Positive: concrete receiver, `returns(true)` contract → the assertion of the
// result verifies from the contract axiom (was a hard Error before Slice 1).
const POSITIVE: &str = r#"
#[trust_vc::trait_spec]
trait AlwaysOk { #[trust_vc::returns(true)] fn ok(&self) -> bool; }
struct Widget(i32);
#[trust_vc::trait_impl]
impl AlwaysOk for Widget { fn ok(&self) -> bool { true } }
#[trust_vc::ensures(true)]
fn uses_contract(w: Widget) { let r = w.ok(); trust_vc::assert!(r); }
"#;

#[test]
fn concrete_receiver_resolves_to_trait_contract() {
    let r = verify(POSITIVE, "uses_contract");
    assert!(
        matches!(r, VerifyResult::Verified),
        "concrete trait-method call should verify from the contract, got {r:?}"
    );
}

// Body NOT leaked: contract `result >= 0` is strictly weaker than the body
// value `5`. The contract fact verifies; the body value does NOT — proving the
// impl body is never emitted as a value axiom.
const WEAKER_CONTRACT: &str = r#"
#[trust_vc::trait_spec]
trait NonNeg { #[trust_vc::ensures(result >= 0)] fn v(&self) -> i32; }
struct Cell(i32);
#[trust_vc::trait_impl]
impl NonNeg for Cell { fn v(&self) -> i32 { 5 } }
#[trust_vc::ensures(true)]
fn contract_fact(c: Cell) { let r = c.v(); trust_vc::assert!(r >= 0); }
#[trust_vc::ensures(true)]
fn body_value(c: Cell) { let r = c.v(); trust_vc::assert!(r == 5); }
"#;

#[test]
fn contract_fact_verifies() {
    let r = verify(WEAKER_CONTRACT, "contract_fact");
    assert!(
        matches!(r, VerifyResult::Verified),
        "contract fact should verify, got {r:?}"
    );
}

#[test]
fn impl_body_value_is_not_leaked() {
    let r = verify(WEAKER_CONTRACT, "body_value");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "SOUNDNESS: impl body value must NOT be provable (only the contract is), got {r:?}"
    );
}

// CARDINAL soundness gate: an impl whose BODY VIOLATES its contract must be
// REFUTED by its conformance obligation. That refutation is the load-bearing
// assumption that makes assuming the contract axiom sound — a caller may assume
// the declared contract (as in Verus) precisely BECAUSE the impl is checked
// against it, and the file fails when it is not. Attribution moved the blame to
// the impl's own obligation, never removed the check.
const VIOLATING_IMPL: &str = r#"
#[trust_vc::trait_spec]
trait MustBePos { #[trust_vc::ensures(result > 0)] fn get(&self) -> i32; }
struct Bad(i32);
#[trust_vc::trait_impl]
impl MustBePos for Bad { fn get(&self) -> i32 { -1 } }
#[trust_vc::ensures(true)]
fn assumes_false_contract(b: Bad) { let r = b.get(); trust_vc::assert!(r > 0); }
"#;

#[test]
fn contract_violating_impl_does_not_let_caller_verify() {
    let r = conformance_verdict(VIOLATING_IMPL, "assumes_false_contract");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL FALSE-VERIFY: the impl body violates the contract callers assume, yet its \
         conformance obligation discharged, got {r:?}"
    );
}

// Two distinct impls with OPPOSITE contracts must stay independent: each impl's
// own contract verifies, but neither imports the other's.
const TWO_IMPLS: &str = r#"
#[trust_vc::trait_spec]
trait Pos { #[trust_vc::ensures(result > 0)] fn m(&self) -> i32; }
#[trust_vc::trait_spec]
trait Neg { #[trust_vc::ensures(result < 0)] fn m(&self) -> i32; }
struct Alpha(i32);
struct Beta(i32);
#[trust_vc::trait_impl]
impl Pos for Alpha { fn m(&self) -> i32 { 1 } }
#[trust_vc::trait_impl]
impl Neg for Beta { fn m(&self) -> i32 { -1 } }
#[trust_vc::ensures(true)]
fn alpha_pos(a: Alpha) { let r = a.m(); trust_vc::assert!(r > 0); }
#[trust_vc::ensures(true)]
fn alpha_cross(a: Alpha) { let r = a.m(); trust_vc::assert!(r < 0); }
"#;

#[test]
fn distinct_impl_contract_verifies() {
    let r = verify(TWO_IMPLS, "alpha_pos");
    assert!(
        matches!(r, VerifyResult::Verified),
        "Alpha's own contract should verify, got {r:?}"
    );
}

#[test]
fn distinct_impls_do_not_cross_leak() {
    let r = verify(TWO_IMPLS, "alpha_cross");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "SOUNDNESS: Alpha must not import Beta's (opposite) contract, got {r:?}"
    );
}

// UFCS / path-call forms resolve to the SAME contract axiom as the receiver
// form (Slice 1b): `<S as Tr>::f(s)`, `S::f(s)`, and `Tr::f(s)` all funnel
// through the concrete-impl MethodMeta keyed on the receiver's type.
const UFCS_POSITIVE: &str = r#"
#[trust_vc::trait_spec]
trait Pos { #[trust_vc::ensures(result > 0)] fn v(&self) -> i32; }
struct Widget(i32);
#[trust_vc::trait_impl]
impl Pos for Widget { fn v(&self) -> i32 { 10 } }
#[trust_vc::ensures(true)]
fn via_qself(s: Widget) { let r = <Widget as Pos>::v(&s); trust_vc::assert!(r > 0); }
#[trust_vc::ensures(true)]
fn via_typepath(s: Widget) { let r = Widget::v(&s); trust_vc::assert!(r > 0); }
#[trust_vc::ensures(true)]
fn via_traitpath(s: Widget) { let r = Pos::v(&s); trust_vc::assert!(r > 0); }
"#;

#[test]
fn ufcs_qself_form_resolves() {
    assert!(matches!(
        verify(UFCS_POSITIVE, "via_qself"),
        VerifyResult::Verified
    ));
}
#[test]
fn ufcs_type_path_form_resolves() {
    assert!(matches!(
        verify(UFCS_POSITIVE, "via_typepath"),
        VerifyResult::Verified
    ));
}
#[test]
fn ufcs_trait_path_form_resolves() {
    assert!(matches!(
        verify(UFCS_POSITIVE, "via_traitpath"),
        VerifyResult::Verified
    ));
}

// UFCS body-not-leaked: contract `result >= 0` weaker than body `5`; via UFCS
// the body value `== 5` must NOT be provable (own fixture — no cross-taint).
const UFCS_WEAKER: &str = r#"
#[trust_vc::trait_spec]
trait NonNeg { #[trust_vc::ensures(result >= 0)] fn w(&self) -> i32; }
struct Gadget(i32);
#[trust_vc::trait_impl]
impl NonNeg for Gadget { fn w(&self) -> i32 { 5 } }
#[trust_vc::ensures(true)]
fn ufcs_body(s: Gadget) { let r = <Gadget as NonNeg>::w(&s); trust_vc::assert!(r == 5); }
"#;

#[test]
fn ufcs_impl_body_value_is_not_leaked() {
    let r = verify(UFCS_WEAKER, "ufcs_body");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "SOUNDNESS: UFCS body value must not be provable, got {r:?}"
    );
}

// UFCS cardinal gate: a contract-violating impl reached via UFCS must still be
// refuted by its conformance obligation (own fixture so the conformance CE is
// unambiguous).
const UFCS_VIOLATING: &str = r#"
#[trust_vc::trait_spec]
trait MustBePos { #[trust_vc::ensures(result > 0)] fn g(&self) -> i32; }
struct Rotten(i32);
#[trust_vc::trait_impl]
impl MustBePos for Rotten { fn g(&self) -> i32 { -1 } }
#[trust_vc::ensures(true)]
fn ufcs_bad(s: Rotten) { let r = <Rotten as MustBePos>::g(&s); trust_vc::assert!(r > 0); }
"#;

#[test]
fn ufcs_contract_violating_impl_does_not_verify() {
    let r = conformance_verdict(UFCS_VIOLATING, "ufcs_bad");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: the UFCS-reached impl body violates the contract callers assume, yet its \
         conformance obligation discharged, got {r:?}"
    );
}

// Regression guard: the generic trait-bound path (already sound before Slice 1)
// stays byte-for-byte unchanged — a generic receiver passes bare (no box).
const GENERIC: &str = r#"
#[trust_vc::trait_spec]
trait GenOk { #[trust_vc::returns(true)] fn ok(&self) -> bool; }
struct Gw(i32);
#[trust_vc::trait_impl]
impl GenOk for Gw { fn ok(&self) -> bool { true } }
#[trust_vc::ensures(true)]
fn generic_caller<T: GenOk>(t: T) { let r = t.ok(); trust_vc::assert!(r); }
"#;

#[test]
fn generic_path_unchanged() {
    let r = verify(GENERIC, "generic_caller");
    assert!(
        matches!(r, VerifyResult::Verified),
        "generic path regression, got {r:?}"
    );
}

// impl-ensures capability (#34): a trait impl may STRENGTHEN its postcondition
// with its own `#[trust_vc::ensures]`, captured, conformance-verified
// (`body ⊨ impl_ensures`), and propagated to concrete (struct) callers alongside
// the trait contract. These PIN the soundness envelope: value comes only from
// the declared contract (trait + impl ensures), NEVER the impl body; and a body
// that violates its declared ensures Counterexamples (conformance gates it).
const IMPL_ENSURES: &str = r#"
#[trust_vc::trait_spec]
trait Ranged { #[trust_vc::ensures(result >= 10)] fn r(&self) -> i32; }
struct Gadget(i32);
#[trust_vc::trait_impl]
impl Ranged for Gadget { #[trust_vc::ensures(result <= 20)] fn r(&self) -> i32 { 15 } }
#[trust_vc::ensures(true)]
fn uses_both_bounds(g: Gadget) { let x = g.r(); trust_vc::assert!(x >= 10 && x <= 20); }
#[trust_vc::ensures(true)]
fn body_value(g: Gadget) { let x = g.r(); trust_vc::assert!(x == 15); }
#[trust_vc::ensures(true)]
fn beyond_contract(g: Gadget) { let x = g.r(); trust_vc::assert!(x >= 12); }
"#;

#[test]
fn impl_ensures_reaches_concrete_caller() {
    // Both the trait ensures (>=10) and the impl-extended ensures (<=20) verify.
    assert!(matches!(
        verify(IMPL_ENSURES, "uses_both_bounds"),
        VerifyResult::Verified
    ));
}

#[test]
fn impl_ensures_does_not_leak_the_body() {
    // The exact body value (15) is NOT provable — only the declared contract is.
    let r = verify(IMPL_ENSURES, "body_value");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "impl body value leaked: {r:?}"
    );
}

#[test]
fn impl_ensures_no_claim_beyond_contract() {
    // >=12 is entailed by neither >=10 nor <=20; only the leaked body would satisfy.
    let r = verify(IMPL_ENSURES, "beyond_contract");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "claim beyond contract verified: {r:?}"
    );
}

// CARDINAL: an impl whose body VIOLATES its declared ensures must be refuted by
// its conformance obligation — the impl-ensures is conformance-VERIFIED before
// any caller may assume it.
const IMPL_ENSURES_VIOLATING: &str = r#"
#[trust_vc::trait_spec]
trait Cap { #[trust_vc::ensures(result >= 0)] fn cap(&self) -> i32; }
struct Widget(i32);
#[trust_vc::trait_impl]
impl Cap for Widget { #[trust_vc::ensures(result <= 20)] fn cap(&self) -> i32 { 25 } }
#[trust_vc::ensures(true)]
fn assumes_violated_ensures(w: Widget) { let r = w.cap(); trust_vc::assert!(r <= 20); }
"#;

#[test]
fn violating_impl_ensures_does_not_verify() {
    let r = conformance_verdict(IMPL_ENSURES_VIOLATING, "assumes_violated_ensures");
    assert!(
        !matches!(r, VerifyResult::Verified),
        "CARDINAL: the impl-ensures (<=20) that callers assume is violated by the body (25), \
         yet its conformance obligation discharged: {r:?}"
    );
}
