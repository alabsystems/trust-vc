// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A3: inherent-impl method / associated-fn / `Self::`-call return-type
//! registration. These pin that a referenced inherent method's call value gets
//! a type and (for pure single-return bodies) a sound definitional axiom, so
//! the upstream-shaped impl-call cases verify — and that WRONG assertions about
//! those call values never falsely verify (fail-closed soundness guards).

use super::*;

fn verify_src(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).unwrap();
    let f = find_function(&file, func).unwrap();
    match extract_verification_conditions_with_file_context(&file, f) {
        Ok(vc) => vc.verify(),
        Err(e) => VerifyResult::Error {
            message: e.to_string(),
        },
    }
}

/// `recv.method(args)` for an inherent `&self` method resolves to a typed call
/// and its pure single-return body axiom lets the postcondition verify.
#[test]
fn inherent_ref_self_method_call_verifies() {
    let code = r#"
        struct TemplateCar { passengers: u64, }
        impl TemplateCar {
            fn template_get_passengers(&self) -> u64 { self.passengers }
        }
        fn test1(c3: TemplateCar) {
            let p3 = c3.template_get_passengers();
            assert!(p3 == c3.passengers);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test1"), VerifyResult::Verified),
        "inherent &self method call should verify, got {:?}",
        verify_src(code, "test1")
    );
}

/// SOUNDNESS GUARD: a WRONG assertion about the `&self` method's result must NOT
/// verify (it lowers via the same body axiom, which constrains the value to the
/// real field — so the false claim fails closed).
#[test]
fn inherent_ref_self_method_call_wrong_assertion_fails_closed() {
    let code = r#"
        struct TemplateCar { passengers: u64, }
        impl TemplateCar {
            fn template_get_passengers(&self) -> u64 { self.passengers }
        }
        fn test1(c3: TemplateCar) {
            let p3 = c3.template_get_passengers();
            assert!(p3 == 999u64);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test1"), VerifyResult::Verified),
        "wrong assertion about &self method result must not verify"
    );
}

/// `recv.method()` for a by-value `self` method resolves and verifies.
#[test]
fn inherent_value_self_method_call_verifies() {
    let code = r#"
        struct TemplateCar { the_v: u64, }
        impl TemplateCar {
            fn template_get_v(self) -> u64 { self.the_v }
        }
        fn test1(c3: TemplateCar) {
            let v = c3.template_get_v();
            assert!(v == c3.the_v);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test1"), VerifyResult::Verified),
        "by-value self method call should verify, got {:?}",
        verify_src(code, "test1")
    );
}

/// `Type::assoc()` associated (no-self) constructor-style call resolves to a
/// typed call and its body axiom lets a field assertion verify.
#[test]
fn inherent_associated_fn_call_verifies() {
    let code = r#"
        struct TemplateCar { passengers: u64, }
        impl TemplateCar {
            fn template_new() -> TemplateCar { TemplateCar { passengers: 205 } }
        }
        fn test1() {
            let c3 = TemplateCar::template_new();
            assert!(c3.passengers == 205u64);
        }
    "#;
    assert!(
        matches!(verify_src(code, "test1"), VerifyResult::Verified),
        "associated fn call should verify, got {:?}",
        verify_src(code, "test1")
    );
}

/// SOUNDNESS GUARD: a wrong assertion about the associated fn's result must NOT
/// verify.
#[test]
fn inherent_associated_fn_call_wrong_assertion_fails_closed() {
    let code = r#"
        struct TemplateCar { passengers: u64, }
        impl TemplateCar {
            fn template_new() -> TemplateCar { TemplateCar { passengers: 205 } }
        }
        fn test1() {
            let c3 = TemplateCar::template_new();
            assert!(c3.passengers == 7u64);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "test1"), VerifyResult::Verified),
        "wrong assertion about associated fn result must not verify"
    );
}

/// `Type::method(recv, args)` associated form with an explicit receiver argument
/// resolves and verifies (upstream `test_resolve_self_ty`-shaped, called from a
/// free function so there is no target-`self` typing dependency).
#[test]
fn inherent_associated_method_with_explicit_receiver_verifies() {
    let code = r#"
        struct Foo { x: u64, }
        impl Foo {
            fn bar(self) -> Foo { self }
        }
        fn caller(f: Foo) {
            let g = Foo::bar(f);
            assert!(g.x == f.x);
        }
    "#;
    assert!(
        matches!(verify_src(code, "caller"), VerifyResult::Verified),
        "associated method call with explicit receiver should verify, got {:?}",
        verify_src(code, "caller")
    );
}

/// SOUNDNESS GUARD: a METHOD-LEVEL generic (`fn take<B>`) is a separate axis and
/// must remain fail-closed even after Phase A2-generic reinstated monomorphizing
/// a fully-generic IMPL (`impl<A> Base<A>`) on a concrete receiver. The impl here
/// is non-generic; only the method carries `<B>`, so it is skipped at
/// registration and the call's return type stays unregistered ("unknown return
/// type"), never silently typed.
#[test]
fn generic_inherent_impl_call_remains_fail_closed() {
    let code = r#"
        struct Wrapper { v: u64, }
        impl Wrapper {
            fn take<B>(self, b: B) -> u64 { self.v }
        }
        fn caller(w: Wrapper) {
            let r = Wrapper::take(w, 12u64);
            assert!(r == w.v);
        }
    "#;
    // The method has its own generic param `<B>`, so it is skipped; the call
    // stays blocked (not Verified, never a false Verified).
    assert!(
        !matches!(verify_src(code, "caller"), VerifyResult::Verified),
        "generic-method inherent call must remain fail-closed, got {:?}",
        verify_src(code, "caller")
    );
}

/// SOUNDNESS GUARD: a method whose body is NOT a single pure return expression
/// gets type-only registration (no body axiom), so an assertion about its value
/// fails closed rather than being assumed from an unsound body inline.
#[test]
fn non_single_return_body_is_type_only_and_fails_closed() {
    let code = r#"
        struct Counter { n: u64, }
        impl Counter {
            fn bump(&self) -> u64 {
                let mut x = self.n;
                x = x + 1u64;
                x
            }
        }
        fn caller(c: Counter) {
            let r = c.bump();
            assert!(r == c.n);
        }
    "#;
    assert!(
        !matches!(verify_src(code, "caller"), VerifyResult::Verified),
        "multi-statement body must be type-only (no axiom) and fail closed"
    );
}
