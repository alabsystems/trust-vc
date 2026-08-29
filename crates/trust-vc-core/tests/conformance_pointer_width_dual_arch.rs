// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FV-4 regression: the trait-impl CONFORMANCE lane must honour the #2778
//! dual-arch pointer-width rule, exactly as the FUNCTION lane does.
//!
//! `verify_function_from_file` implements the rule (`vc_extraction.rs`): a unit
//! with no `global size_of usize` directive whose proof depends on the pointer
//! width is verified at BOTH a 32-bit and a 64-bit `usize`, because Rust permits
//! both and a proof is sound only if it holds at every width the target may
//! have.
//!
//! `verify_trait_conformance_obligation` did NOT. It installed only the pinned
//! directive width (`pinned_width.map(PointerWidthGuard::install)`) and
//! otherwise left the host's width in force, so on a 64-bit host a trait-impl
//! obligation that is FALSE at a 32-bit `usize` came back `Verified`. This is
//! the impl's ONLY report channel — a function's verdict deliberately no longer
//! inherits a sibling impl's conformance verdict — so nothing else refutes it.
//!
//! The two round-1 fixes in this family widened the width PREDICATE
//! (`ir::unit_is_pointer_width_polymorphic`) and de-duplicated its two copies.
//! Neither widened its CALLERS, and the conformance lane never called it at all.
//!
//! Probe 1 is the cardinal guard. Probes 2-4 are the narrowness pins: a
//! conformance obligation true at both widths must still verify, a
//! width-invariant one must be untouched, and an explicit directive must still
//! pin the target.

use trust_vc_core::{
    list_trait_conformance_obligations, verify_trait_conformance_obligation, VerifyResult,
};

/// Unique temp path per fixture: fixtures reuse trait/impl names, so a
/// name-keyed path would let parallel tests race on one file.
fn write_fixture(src: &str, case: &str) -> std::path::PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let mut path = std::env::temp_dir();
    path.push(format!(
        "tvc_conf_width_{}_{}_{case}.rs",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, src).expect("write fixture");
    path
}

/// Enumerate the file's conformance obligations, then verify the one whose name
/// contains `needle` — the same address-by-name flow `cargo trust-vc check`
/// drives. Enumerating first also pins that the obligation is REACHABLE: a
/// "rejected" verdict for a name that was never listed would prove nothing.
fn conformance_verdict(src: &str, case: &str, needle: &str) -> VerifyResult {
    let path = write_fixture(src, case);
    let out = (|| {
        let names = match list_trait_conformance_obligations(path.to_str().unwrap()) {
            Ok(names) => names,
            Err(err) => {
                return VerifyResult::Error {
                    message: format!("listing failed: {err}"),
                }
            }
        };
        let Some(name) = names.iter().find(|n| n.contains(needle)) else {
            return VerifyResult::Error {
                message: format!("no conformance obligation matching {needle:?}; got {names:?}"),
            };
        };
        match verify_trait_conformance_obligation(path.to_str().unwrap(), name) {
            Ok(result) => result,
            Err(err) => VerifyResult::Error {
                message: err.to_string(),
            },
        }
    })();
    let _ = std::fs::remove_file(&path);
    out
}

/// A trait `ensures` the impl body satisfies at a 64-bit `usize` and violates at
/// a 32-bit one: `x * 2` with `x <= 4294967295` overflows a 32-bit `usize`, so
/// `result >= x` is false there.
///
/// TWO impls, deliberately. With a single impl the FUNCTION lane resolves the
/// trait declaration to that unique body and refutes it there, masking the
/// conformance hole. With two, the function lane is silent and the whole file
/// reported `verified` before the fix.
const DOUBLER: &str = r#"
#[trust_vc::trait_spec]
trait Doubler {
    #[trust_vc::requires(x <= 4294967295)]
    #[trust_vc::ensures(result >= x)]
    fn dbl(x: usize) -> usize;
}

struct Honest;
struct Wide;

#[trust_vc::trait_impl]
impl Doubler for Honest {
    fn dbl(x: usize) -> usize { x }
}

#[trust_vc::trait_impl]
impl Doubler for Wide {
    fn dbl(x: usize) -> usize { x * 2 }
}
"#;

/// Probe 1 (CARDINAL) — the 32-bit-false conformance obligation must not verify.
///
/// Over-rejection is acceptable here (`Counterexample` or a fail-closed
/// `Unknown`), but `Error` is not: that would mean the probe failed for
/// infrastructure reasons and proved nothing.
#[test]
fn conformance_false_at_32_bits_does_not_verify() {
    let verdict = conformance_verdict(DOUBLER, "cardinal", "Doubler::dbl for Wide");
    assert!(
        matches!(
            verdict,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "an impl whose body violates its trait `ensures` at a 32-bit usize must \
         not report Verified; got {verdict:?}"
    );
}

/// Probe 2 (NARROWNESS) — the honest impl in the SAME width-polymorphic file
/// conforms at both widths and must still verify. Rejecting every obligation in
/// a file that mentions `usize` would pass probe 1 and fail here.
#[test]
fn conformance_true_at_both_widths_in_the_same_file_still_verifies() {
    let verdict = conformance_verdict(DOUBLER, "narrow_sibling", "Doubler::dbl for Honest");
    assert!(
        matches!(verdict, VerifyResult::Verified),
        "the conforming sibling impl must still verify; got {verdict:?}"
    );
}

/// Probe 3 (NARROWNESS) — a width-polymorphic obligation that is genuinely true
/// at 32 AND 64 bits. `x + 1` under `x < 100` cannot overflow at either width,
/// so both passes discharge and the combined verdict stays `Verified`.
#[test]
fn conformance_width_polymorphic_but_true_everywhere_verifies() {
    const INC: &str = r#"
#[trust_vc::trait_spec]
trait Inc {
    #[trust_vc::requires(x < 100)]
    #[trust_vc::ensures(result > x)]
    fn inc(x: usize) -> usize;
}

struct S;

#[trust_vc::trait_impl]
impl Inc for S {
    fn inc(x: usize) -> usize { x + 1 }
}
"#;
    let verdict = conformance_verdict(INC, "narrow_dual_true", "Inc::inc for S");
    assert!(
        matches!(verdict, VerifyResult::Verified),
        "a conformance obligation true at both widths must verify; got {verdict:?}"
    );
}

/// Probe 4 (NARROWNESS) — a `u32` obligation names no `usize`/`isize`, so the
/// file stays on the single-solve plan and its verdict is unchanged.
#[test]
fn conformance_without_pointer_width_is_unchanged() {
    const ADDER: &str = r#"
#[trust_vc::trait_spec]
trait Adder {
    #[trust_vc::requires(x <= 100)]
    #[trust_vc::ensures(result >= x)]
    fn add(x: u32) -> u32;
}

struct Plain;

#[trust_vc::trait_impl]
impl Adder for Plain {
    fn add(x: u32) -> u32 { x + 1 }
}
"#;
    let verdict = conformance_verdict(ADDER, "narrow_invariant", "Adder::add for Plain");
    assert!(
        matches!(verdict, VerifyResult::Verified),
        "a width-invariant conformance obligation must be untouched; got {verdict:?}"
    );
}

/// Probe 5 (NARROWNESS) — `global size_of usize == 8` pins the target
/// architecture, so the otherwise-rejected impl verifies again. The dual path
/// must never override an explicit directive; that would make the directive
/// unusable.
#[test]
fn conformance_pinned_directive_still_wins() {
    let mut src = String::from("global size_of usize == 8;\n");
    src.push_str(DOUBLER);
    let verdict = conformance_verdict(&src, "narrow_pinned", "Doubler::dbl for Wide");
    assert!(
        matches!(verdict, VerifyResult::Verified),
        "an explicit 64-bit directive must pin the conformance lane too; got {verdict:?}"
    );
}

/// Probe 6 (DIRECTIONAL CONTROL) — with the target pinned to 32 bits the SAME
/// impl is refuted, proving the obligation really is width-dependent and that
/// the machinery can see the violation. Without this, probe 1 passing could mean
/// the obligation is simply unprovable at any width.
#[test]
fn conformance_pinned_to_32_bits_is_refuted() {
    let mut src = String::from("global size_of usize == 4;\n");
    src.push_str(DOUBLER);
    let verdict = conformance_verdict(&src, "control_pinned32", "Doubler::dbl for Wide");
    assert!(
        matches!(verdict, VerifyResult::Counterexample { .. }),
        "pinned to 32 bits the impl must be refuted outright; got {verdict:?}"
    );
}
