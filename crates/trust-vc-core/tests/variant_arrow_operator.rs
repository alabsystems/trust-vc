// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Verus variant spec DSL: `e->field` field projection over any datatype
//! (previously Result-only `->Ok_0`/`->Err_0`). A marker resolves at lowering to
//! the owning variant's NATIVE selector — total-but-unconstrained off its
//! constructor, so the off-variant value is unconstrained (SOUND). Positives
//! Verify; liar + off-variant projections fail-closed.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verify(id: &str, func: &str, src: &str) -> VerifyResult {
    let mut p = std::env::temp_dir();
    p.push(format!("tvc_va_{}_{}.rs", std::process::id(), id));
    std::fs::write(&p, src).expect("write fixture");
    let r = verify_function_from_file(p.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    });
    let _ = std::fs::remove_file(&p);
    r
}
fn verified(r: &VerifyResult) -> bool {
    matches!(r, VerifyResult::Verified)
}

const SRC: &str = r#"
enum E { A(u64), B }
enum CustomResultNames { Ok(u64), Err(u64) }
enum TwoPayloads { Left(u64), Right(u64) }
enum TwoNamed { First { value: u64 }, Second { value: u64 } }
#[trust_vc::ensures(result is A ==> result->0 == 5u64)]
fn arrow_pos() -> E { E::A(5u64) }
#[trust_vc::ensures(result is A ==> result->0 == 6u64)]
fn arrow_liar() -> E { E::A(5u64) }
#[trust_vc::ensures(result is Some ==> result->0 == 5u64)]
fn arrow_option() -> Option<u64> { Some(5u64) }
#[trust_vc::ensures(result->0 == 5u64)]
fn arrow_off_variant() -> E { E::B }
#[trust_vc::ensures(result is Ok ==> result->Ok_0 == 5u64)]
fn arrow_result_regression() -> Result<u64, u64> { Result::Ok(5u64) }
#[trust_vc::ensures(result is Ok ==> result->Ok_0 == 13u64)]
fn arrow_custom_ok() -> CustomResultNames { CustomResultNames::Ok(13u64) }
#[trust_vc::ensures(result is Err ==> result->Err_0 == 17u64)]
fn arrow_custom_err() -> CustomResultNames { CustomResultNames::Err(17u64) }
#[trust_vc::ensures(result is Left ==> result->Left_0 == 7u64)]
fn arrow_qualified_tuple() -> TwoPayloads { TwoPayloads::Left(7u64) }
#[trust_vc::ensures(result is First ==> result->First_value == 9u64)]
fn arrow_qualified_named() -> TwoNamed { TwoNamed::First { value: 9u64 } }
#[trust_vc::ensures(result is Some ==> result->Some_0 is Some ==> result->Some_0->Some_0 == 11u64)]
fn arrow_chain() -> Option<Option<u64>> { Some(Some(11u64)) }
"#;

#[test]
fn arrow_projection_verifies_and_liar_fails_closed() {
    assert!(
        verified(&verify("p", "arrow_pos", SRC)),
        "result is A ==> result->0 == 5 must verify"
    );
    assert!(
        !verified(&verify("l", "arrow_liar", SRC)),
        "CARDINAL: ==> result->0 == 6 (field is 5) must NOT verify"
    );
    assert!(
        verified(&verify("o", "arrow_option", SRC)),
        "Option result->0 must verify"
    );
}

#[test]
fn arrow_off_variant_is_unconstrained_sound() {
    // result is B (no field 0) => result->0 is UNCONSTRAINED; must NOT verify.
    assert!(
        !verified(&verify("s", "arrow_off_variant", SRC)),
        "CARDINAL: result->0 on the off-variant (B) must be unconstrained (never a false-verify)"
    );
}

#[test]
fn arrow_result_form_still_works() {
    let result_projection = verify("r", "arrow_result_regression", SRC);
    assert!(
        verified(&result_projection),
        "existing Result `->Ok_0` must still verify, got {result_projection:?}"
    );
    let custom_projection = verify("cr", "arrow_custom_ok", SRC);
    assert!(
        verified(&custom_projection),
        "an `Ok_0` spelling on a custom datatype must use that datatype's selector, got {custom_projection:?}"
    );
    let custom_err_projection = verify("ce", "arrow_custom_err", SRC);
    assert!(
        verified(&custom_err_projection),
        "an `Err_0` spelling on a custom datatype must use that datatype's selector, got {custom_err_projection:?}"
    );
}

#[test]
fn arrow_variant_qualified_fields_and_chains_work() {
    assert!(
        verified(&verify("qt", "arrow_qualified_tuple", SRC)),
        "variant-qualified tuple field must disambiguate duplicate index 0"
    );
    assert!(
        verified(&verify("qn", "arrow_qualified_named", SRC)),
        "variant-qualified named field must disambiguate duplicate `value` fields"
    );
    assert!(
        verified(&verify("ch", "arrow_chain", SRC)),
        "postfix `->` trailers must retain the first projection as the second receiver"
    );
}
