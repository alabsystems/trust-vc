//! Native match control, bindings, proof obligations and mode boundaries.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod common;

fn checked(name: &str, source: &str) {
    let result = common::run(name, source, &[]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
}

fn checked_new(name: &str, source: &str) -> common::Run {
    let result = common::run(name, source, &["-V", "new-mut-ref"]);
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    assert!(result.errors().is_empty(), "{result:?}");
    result
}

fn function_sites(result: &common::Run, name: &str, proved: u64, failed: u64) {
    let function = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == name)
        .unwrap_or_else(|| panic!("missing {name}: {result:?}"));
    assert_eq!(function["sites_proved"], proved, "{result:?}");
    assert_eq!(function["sites_failed"], failed, "{result:?}");
}

#[test]
fn booleans_literals_wildcards_and_bound_values_keep_both_arms() {
    checked(
        "match_scalars",
        "verus! {
        fn bit(b: bool) -> (r: u8) ensures r == if b { 1u8 } else { 2u8 }, {
            match b { true => 1u8, false => 2u8 }
        }
        fn byte(x: u8) -> (r: u8) ensures x == 0 ==> r == 1, x != 0 ==> r == x, {
            match x { 0 => 1u8, other => other }
        }
        fn rest(v: (u8, bool, u16)) -> (r: u8) ensures r == v.0, {
            match v { (x, ..) => x }
        }
        fn caller() {
            let a = bit(true); let b = bit(false);
            assert(a == 1); assert(b == 2);
            let c = byte(0); let d = byte(9);
            assert(c == 1); assert(d == 9);
        }
    }",
    );
}

#[test]
fn native_enum_fields_are_selected_from_the_actual_variant() {
    checked(
        "match_variants",
        "verus! {
        enum E { One(u8), Pair { first: u8, second: u8 }, Empty }
        enum Rest { Values(u8, u8), Empty }
        fn first(e: Rest) -> (r: u8)
            ensures r == (match e { Rest::Values(x, ..) => x, Rest::Empty => 0u8 }),
        { match e { Rest::Values(x, ..) => x, Rest::Empty => 0u8 } }
        fn get(e: E) -> (r: u8)
            ensures r == (match e { E::One(x) => x, E::Pair { first: _, second } => second, E::Empty => 0u8 }),
        {
            match e { E::One(x) => x, E::Pair { first: _, second } => second, E::Empty => 0u8 }
        }
        fn brace(e: E) requires e is Pair, e->Pair_second == 9, {
            let selected = get(e); assert(selected == 9);
        }
        fn caller() {
            let one = get(E::One(7)); assert(one == 7);
            let first_value = first(Rest::Values(7, 11)); assert(first_value == 7);
            let empty_rest = first(Rest::Empty); assert(empty_rest == 0);
            let empty = get(E::Empty); assert(empty == 0);
        }
    }",
    );
}

#[test]
fn pure_matches_bind_nested_variants_in_headers_and_assertions() {
    checked(
        "match_pure",
        "verus! {
        enum O<T> { Some(T), None }
        fn good(o: O<O<u8>>)
            requires match o { O::Some(O::Some(x)) => x < 5, _ => true },
        {
            assert(match o { O::Some(O::Some(x)) => x < 5, _ => true });
        }
        fn tuple(v: (u8, bool)) {
            let ghost x = match v { (n, true) => n, _ => 0u8 };
            assert(x <= 255);
        }
    }",
    );
}

#[test]
fn false_arm_relations_remain_failed_obligations() {
    let result = common::run(
        "match_false",
        "verus! {
        enum E { A(u8), B(u8) }
        fn scalar(b: bool) { let x = match b { true => 1u8, false => 2u8 }; assert(x == 0); }
        fn variant(e: E) { let x = match e { E::A(n) => n, E::B(n) => n }; assert(x > 0); }
    }",
        &[],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 2, "{result:?}");
}

#[test]
fn scrutinee_call_checks_once_and_arm_effects_stay_conditional() {
    let result = common::run(
        "match_once",
        "verus! {
        fn condition(x: u8) -> (r: bool) requires x > 0, ensures r, { true }
        fn caller(x: u8) requires x > 0, {
            let mut n = 0u8;
            match condition(x) { true => { n = 5; }, false => { n = 9; } }
            assert(n == 5);
        }
    }",
        &[],
    );
    assert_eq!(result.exit, 0, "{result:?}");
    assert_eq!(result.outcome(), "checked", "{result:?}");
    let caller = result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function["def_path"] == "caller")
        .unwrap();
    // One call precondition and one assertion, across both conditional arms.
    assert_eq!(caller["sites_proved"], 2, "{result:?}");
}

#[test]
fn diverging_arms_and_outer_bindings_join_only_on_fallthrough() {
    checked(
        "match_returns",
        "verus! {
        enum E { Stop, Continue }
        fn value(e: E) -> (r: u8) ensures r == 5, {
            let x;
            match e { E::Stop => return 5u8, E::Continue => { x = 5u8; } }
            x
        }
        fn all_return(b: bool) -> (r: u8) ensures r == 3, {
            match b { true => return 3u8, false => return 3u8 }
        }
    }",
    );
    let result = common::run("match_wrong_scope", "verus! {
        fn f(b: bool) { match b { true => { let inside = 1u8; }, false => {} } assert(inside == 1); }
    }", &[]);
    assert_eq!(result.exit, 1, "{result:?}");
    assert!(
        result.record["functions"]
            .as_array()
            .into_iter()
            .flatten()
            .all(|function| function["verdict"] != "verified"),
        "{result:?}"
    );
}

#[test]
fn ghost_control_and_field_values_cannot_leak_into_exec_code() {
    for (name, source) in [
        ("match_ghost_control", "verus! { fn f() -> u8 { let ghost b = true; match b { true => 1, false => 2 } } }"),
        ("match_ghost_field", "verus! { enum E { V(#[verifier::spec] u8) } fn f(e: E) -> u8 { match e { E::V(x) => x } } }"),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(result.record["functions"].as_array().into_iter().flatten()
            .all(|function| function["verdict"] != "verified"), "{result:?}");
        assert!(!result.errors().is_empty(), "{result:?}");
    }
}

#[test]
fn guards_references_or_patterns_and_missing_arms_supply_no_facts() {
    for (name, source) in [
        ("match_guard", "verus! { fn f(x:u8)->u8 {match x { n if n == 0 => 1, _ => 2 }} }"),
        ("match_reference", "verus! { fn f(x:&u8)->u8 {match x { &0 => 1, _ => 2 }} }"),
        ("match_or", "verus! { fn f(x:u8)->u8 {match x { 0 | 1 => 1, _ => 2 }} }"),
        ("match_nonexhaustive", "verus! { fn f(x:bool)->u8 {match x { true => 1 }} }"),
        ("match_opaque", "verus! { #[verifier::external_body] enum E { A, B } fn f(x:E)->u8 {match x { E::A => 1, E::B => 2 }} }"),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(result.record["functions"].as_array().into_iter().flatten()
            .all(|function| function["verdict"] != "verified"), "{result:?}");
    }
}

#[test]
fn assignment_unit_results_keep_actual_modes_and_false_obligations() {
    let result = common::run(
        "assignment_unit_results",
        "verus! {
        fn exec_assignment() {
            let mut x = 0u8;
            let _unit = { x = 1u8 };
            assert(x == 1u8); assert(x == 2u8);
        }
        fn ghost_assignment() {
            let ghost mut x = 0u8;
            proof { x = 1u8 }
            assert(x == 1u8); assert(x == 2u8);
        }
    }",
        &[],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 2, "{result:?}");
    for function in result.record["functions"].as_array().unwrap() {
        assert_eq!(function["sites_proved"], 1, "{result:?}");
        assert_eq!(function["sites_failed"], 1, "{result:?}");
    }
    for (name, source) in [
        (
            "assignment_exec_in_proof",
            "verus! { fn f() { let mut x=0u8; proof { x=1u8 } } }",
        ),
        (
            "assignment_exec_in_spec",
            "verus! { spec fn f()->u8 { let mut x=0u8; x=1u8; x } }",
        ),
    ] {
        let result = common::run(name, source, &[]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(!result.errors().is_empty(), "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .into_iter()
                .flatten()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
}

#[test]
fn stable_local_tuple_struct_and_dereference_places_keep_their_values() {
    let result = checked_new(
        "match_stable_places",
        r#"verus! {
        enum E { Pair(u8, u8), Empty }
        struct Holder { value: E, untouched: u8 }
        fn local(e: E) {
            let n = match e { E::Pair(a, b) => { assert(a <= 255); b }, E::Empty => 0u8 };
            assert(n <= 255);
        }
        fn tuple(p: (E, u8)) {
            let n = match p.0 { E::Pair(a, b) => { assert(a <= 255); b }, E::Empty => 0u8 };
            assert(n <= 255); assert(p.1 <= 255);
        }
        fn field(h: Holder) {
            let n = match h.value { E::Pair(a, b) => { assert(a <= 255); b }, E::Empty => 0u8 };
            assert(n <= 255); assert(h.untouched <= 255);
        }
        fn shared(b: &bool) -> (r: u8) ensures r == if *b { 1u8 } else { 2u8 }, {
            match *b { true => 1u8, false => 2u8 }
        }
    }"#,
    );
    function_sites(&result, "local", 2, 0);
    function_sites(&result, "tuple", 3, 0);
    function_sites(&result, "field", 3, 0);
    function_sites(&result, "shared", 1, 0);

    // A kept &mut parameter still needs the separate native shadow-read
    // availability producer. Preserve this source as an explicit boundary;
    // its refusal must not suppress the supported positive crate above.
    // This remains a missing Verus feature and earns no parity-pass credit.
    let boundary = common::run(
        "match_stable_mut_ref_parameter_boundary",
        r#"verus! {
        fn exclusive(b: &mut bool) {
            let previous = match *b { true => true, false => false };
            assert(previous == *b);
        }
    }"#,
        &["-V", "new-mut-ref"],
    );
    assert_eq!(boundary.exit, 1, "{boundary:?}");
    assert_eq!(boundary.outcome(), "refused", "{boundary:?}");
    assert!(boundary.record["erase_exit"].is_null(), "{boundary:?}");
    let functions = boundary.record["functions"].as_array().unwrap();
    assert!(
        functions
            .iter()
            .all(|function| function["verdict"] != "verified"),
        "{boundary:?}"
    );
    assert!(
        functions.iter().any(|function| {
            function["def_path"] == "exclusive"
                && function["verdict"] == "refused"
                && function["tag"] == "new-mut-ref"
        }),
        "{boundary:?}"
    );
    assert!(
        boundary.errors().iter().any(|error| error.message
            == "trust-vc refused: new-mut-ref: an executable or proof parameter holding `&mut` without native availability and resolution"),
        "{boundary:?}"
    );
}

#[test]
fn stable_projected_patterns_move_only_the_bound_generic_fields() {
    let result = checked_new(
        "match_stable_generic_fields",
        r#"verus! {
        enum E<A, B> { Both(A, B), First(A, B) }
        struct Holder<A, B> { value: E<A, B>, untouched: u8 }
        fn consume<T>(value: T) {}
        fn local<A, B>(e: E<A, B>) {
            assert(e is First ==> has_resolved(e->First_1));
            match e {
                E::Both(a, b) => { consume(a); consume(b); }
                E::First(a, _) => { consume(a); }
            }
        }
        fn tuple<A, B>(p: (E<A, B>, u8)) {
            assert(p.0 is First ==> has_resolved(p.0->First_1));
            match p.0 {
                E::Both(a, b) => { consume(a); consume(b); }
                E::First(a, _) => { consume(a); }
            }
            assert(p.1 <= 255);
        }
        fn field<A, B>(h: Holder<A, B>) {
            assert(h.value is First ==> has_resolved(h.value->First_1));
            match h.value {
                E::Both(a, b) => { consume(a); consume(b); }
                E::First(a, _) => { consume(a); }
            }
            assert(h.untouched <= 255);
        }
    }"#,
    );
    function_sites(&result, "local", 1, 0);
    function_sites(&result, "tuple", 2, 0);
    function_sites(&result, "field", 2, 0);
}

#[test]
fn stable_pattern_consumption_and_missing_variant_guards_stay_false() {
    let result = common::run(
        "match_stable_generic_false",
        r#"verus! {
        enum E<A, B> { Both(A, B), First(A, B) }
        fn consume<T>(value: T) {}
        fn consumed<A, B>(e: E<A, B>) {
            assert(e is First ==> has_resolved(e->First_0));
            match e {
                E::Both(a, b) => { consume(a); consume(b); }
                E::First(a, _) => { consume(a); }
            }
        }
        fn missing_guard<A, B>(e: E<A, B>) {
            assert(has_resolved(e->First_1));
            match e {
                E::Both(a, b) => { consume(a); consume(b); }
                E::First(a, _) => { consume(a); }
            }
        }
    }"#,
        &["-V", "new-mut-ref"],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 2, "{result:?}");
    function_sites(&result, "consumed", 0, 1);
    function_sites(&result, "missing_guard", 0, 1);
}

#[test]
fn computed_scrutinees_run_once_and_scalar_arm_mutation_uses_the_selected_value() {
    for args in [&[][..], &["-V", "new-mut-ref"][..]] {
        let result = common::run(
            if args.is_empty() {
                "match_once_legacy"
            } else {
                "match_once_new"
            },
            r#"verus! {
            enum E { Value(u8), Empty }
            fn computed() {
                let mut count = 0u8;
                let n = match { count = count + 1; E::Value(7) } {
                    E::Value(n) => n, E::Empty => 0u8,
                };
                assert(count == 1); assert(n == 7); assert(count == 2);
            }
            fn scalar(b: bool) {
                let mut current = b;
                match current { true => { current = false; }, false => { current = true; } }
                assert(current == !b); assert(current == b);
            }
        }"#,
            args,
        );
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "verification-failed", "{result:?}");
        assert_eq!(result.errors().len(), 2, "{result:?}");
        // The arithmetic check is also retained, independently of the two
        // true assertions and the false count twin.
        function_sites(&result, "computed", 3, 1);
        function_sites(&result, "scalar", 1, 1);
    }
}

#[test]
fn logical_match_snapshots_remain_observations_under_new_mut_ref() {
    let result = common::run(
        "match_logical_snapshot",
        r#"verus! {
        enum E { A(u8), B(u8) }
        fn observe(e: E) {
            let ghost before = match e { E::A(n) => n, E::B(n) => n };
            let after = match e { E::A(n) => n, E::B(n) => n };
            assert(before == after); assert(before != after);
        }
        fn proof_observe(e: E) {
            proof {
                let before = match e { E::A(n) => n, E::B(n) => n };
                assert(before <= 255); assert(before > 255);
            }
        }
    }"#,
        &["-V", "new-mut-ref"],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verification-failed", "{result:?}");
    assert_eq!(result.errors().len(), 2, "{result:?}");
    function_sites(&result, "observe", 1, 1);
    function_sites(&result, "proof_observe", 1, 1);
}

#[test]
fn stable_match_lowering_does_not_bypass_modes_moves_or_borrow_lifetimes() {
    for (name, source) in [
        (
            "match_stable_ghost_control",
            "verus! { fn f() -> u8 { let ghost b = true; match b { true => 1, false => 2 } } }",
        ),
        (
            "match_stable_ghost_field",
            "verus! { enum E { V(#[verifier::spec] u8) } fn f(e: E) -> u8 { match e { E::V(n) => n } } }",
        ),
        (
            "match_stable_double_move",
            "verus! { enum E<A> { V(A) } fn consume<A>(a: A) {} fn f<A>(e: E<A>) { match e { E::V(a) => { consume(a); consume(a); } } } }",
        ),
        (
            "match_stable_live_borrow",
            "verus! { fn f() { let mut b = true; let r = &mut b; match b { true => {}, false => {} } *r = false; } }",
        ),
    ] {
        let result = common::run(name, source, &["-V", "new-mut-ref"]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert!(!result.errors().is_empty(), "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .into_iter()
                .flatten()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
}

#[test]
fn tracked_match_results_and_transfers_still_require_native_ownership() {
    // Pure by-value transfers now use the complete retained original-MIR
    // proof. Assertions and Spec observations still require erasure; a
    // completed mode observation alone cannot open that boundary.
    let fields = r#"verus! {
        enum E<A, B> { Both(A, B), First(A, B) }
        proof fn consume<T>(tracked value: T) {}
        proof fn check<A, B>(tracked e: E<A, B>) {
            assert(e is First ==> has_resolved(e->First_1));
            match e {
                E::Both(a, b) => { consume(a); consume(b); }
                E::First(a, _) => { consume(a); }
            }
        }
    }"#;
    let returned = r#"verus! {
        enum E<A, B> { Both(A, B), First(A, B) }
        proof fn pick<A, B>(tracked e: E<A, B>) -> (tracked out: A) {
            match e {
                E::Both(a, b) => { assert(has_resolved(b)); a }
                E::First(a, b) => { assert(has_resolved(b)); a }
            }
        }
    }"#;
    let caller = r#"verus! {
        enum E<A, B> { Both(A, B), First(A, B) }
        proof fn consume<T>(tracked value: T) {}
        proof fn pick<A, B>(tracked e: E<A, B>) -> (tracked out: A) {
            match e { E::Both(a, _) => a, E::First(a, _) => a }
        }
        proof fn caller<A, B>(tracked e: E<A, B>) {
            let tracked selected = pick(e);
            consume(selected);
        }
    }"#;
    let spec_result = r#"verus! {
        enum E<A, B> { Both(A, B), First(A, B) }
        proof fn observe<A, B>(tracked e: E<A, B>) -> bool {
            match e {
                E::Both(_, b) => has_resolved(b),
                E::First(_, b) => has_resolved(b),
            }
        }
    }"#;
    for (name, source) in [
        ("match_tracked_fields_true", fields.to_string()),
        (
            "match_tracked_fields_false",
            fields.replace("e->First_1", "e->First_0"),
        ),
        ("match_tracked_return_true", returned.to_string()),
        (
            "match_tracked_return_false",
            returned.replace("assert(has_resolved(b))", "assert(has_resolved(a))"),
        ),
        (
            "match_tracked_caller_false",
            caller.replace(
                "consume(selected);",
                "assert(has_resolved(selected)); consume(selected);",
            ),
        ),
        ("match_tracked_spec_result", spec_result.to_string()),
    ] {
        let result = common::run(name, &source, &["-V", "new-mut-ref"]);
        assert_eq!(result.exit, 1, "{result:?}");
        assert_eq!(result.outcome(), "refused", "{result:?}");
        assert!(
            result.record["functions"]
                .as_array()
                .unwrap()
                .iter()
                .all(|function| function["verdict"] != "verified"),
            "{result:?}"
        );
    }
    checked_new("match_tracked_caller_transfer", caller);
    let moved = caller.replace(
        "consume(selected);",
        "consume(selected); consume(selected);",
    );
    let result = common::run(
        "match_tracked_caller_double_move",
        &moved,
        &["-V", "new-mut-ref"],
    );
    assert_eq!(result.exit, 1, "{result:?}");
    assert_eq!(result.outcome(), "verus-rejected", "{result:?}");
    let errors = result.errors();
    assert_eq!(errors.len(), 1, "{result:?}");
    assert_eq!(errors[0].code.as_deref(), Some("E0382"), "{result:?}");
    assert!(result.record["functions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|function| function["verdict"] != "verified"));
}
