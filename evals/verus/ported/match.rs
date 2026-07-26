// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc port for upstream match.rs cases.
//
// This is intentionally not a full replacement for upstream match.rs. It covers
// concrete match arm selection, enum and tuple-variant/tuple-struct payload binding,
// enum record-variant payload binding, struct/rest pattern projections,
// local destructuring (tuple-struct, enum tuple-variant, struct exact/rest,
// tuple-struct rest), a concrete-instantiation generic-enum match expression,
// one-arm enum matches, literal and
// or-pattern/range-pattern arm selection, stable false witnesses, and fail-closed unsupported
// boundaries.
// Generic enums beyond the concrete-instantiation scout, proof/spec match
// semantics, recursive boxed lists, unreached(),
// nested @ bindings, and broad diagnostic parity remain unsupported.

#![allow(dead_code)]

pub type MatchExpectedCase = (&'static str, &'static str, &'static str, usize);

pub const MATCH_RS_EXPECTED_CASES: &[MatchExpectedCase] = &[
    (
        "match_if_let_expression_verified",
        "test_if_let1 executable if-let expression",
        "verified",
        1,
    ),
    (
        "match_payload_binding_value_verified",
        "test1 Maybe::Some payload binding",
        "verified",
        1,
    ),
    (
        "match_none_arm_selection_verified",
        "test1 Maybe::None arm selection witness",
        "verified",
        1,
    ),
    (
        "match_literal_bool_selection_verified",
        "const_and_literals m_bool_lit true branch",
        "verified",
        1,
    ),
    (
        "match_literal_fallback_value_verified",
        "const_and_literals integer fallback branch",
        "verified",
        1,
    ),
    (
        "match_single_arm_enum_verified",
        "match_single_arm_issue_444 c subset",
        "verified",
        1,
    ),
    (
        "match_struct_rest_payload_verified",
        "test3_struct_dots struct rest projection",
        "verified",
        1,
    ),
    (
        "match_or_pattern_payload_verified",
        "test_or_patterns Foo::Bar/Foo::Qux payload merge subset",
        "verified",
        1,
    ),
    (
        "match_tuple_struct_payload_binding_value_verified",
        "tuple-struct payload binding local",
        "verified",
        1,
    ),
    (
        "match_named_struct_exact_payload_verified",
        "test3_struct exact struct field projection",
        "verified",
        1,
    ),
    (
        "match_literal_integer_specific_arm_verified",
        "const_and_literals test3 integer literal arm selection",
        "verified",
        1,
    ),
    (
        "match_or_pattern_empty_variant_verified",
        "or_pattern_1_disjunct_issue1588 empty fallback witness",
        "verified",
        1,
    ),
    (
        "match_enum_tuple_variant_pair_payload_verified",
        "test3/test3b Pair::Pair payload match-expression subset",
        "verified",
        1,
    ),
    (
        "match_enum_struct_variant_payload_verified",
        "test3_enum_struct Pair::Pair record payload match-expression subset",
        "verified",
        1,
    ),
    (
        "match_leading_or_pattern_single_variant_verified",
        "or_pattern_1_disjunct_issue1588 leading single-disjunct arm",
        "verified",
        1,
    ),
    (
        "match_range_pattern_expression_verified",
        "pattern_ranges executable range pattern",
        "verified",
        1,
    ),
    (
        "match_spec_range_expression_verified",
        "pattern_ranges spec match expression",
        "verified",
        1,
    ),
    (
        "match_proof_guard_statement_verified",
        "proof-mode guarded match statement",
        "verified",
        1,
    ),
    (
        "match_plain_tuple_local_pattern_verified",
        "test4 tuple local pattern boundary",
        "verified",
        2,
    ),
    (
        "match_tuple_struct_local_destructure_verified",
        "test3_tuple_struct local destructuring boundary",
        "verified",
        3,
    ),
    (
        "match_enum_tuple_variant_local_destructure_verified",
        "test3/test3b Pair::Pair local destructuring boundary",
        "verified",
        3,
    ),
    (
        "match_tuple_struct_rest_local_destructure_verified",
        "dot_dot_patterns tuple constructor rest destructuring boundary",
        "verified",
        6,
    ),
    (
        "match_struct_rest_local_destructure_verified",
        "test3_struct_dots local struct rest destructuring boundary",
        "verified",
        2,
    ),
    (
        "match_struct_exact_local_destructure_verified",
        "test3_struct local exact struct destructuring boundary",
        "verified",
        3,
    ),
    (
        "match_generic_enum_expression_verified",
        "test1 Maybe<A> generic enum match boundary",
        "verified",
        1,
    ),
    (
        "match_plain_tuple_pattern_expression_verified",
        "plain tuple match-expression pattern boundary",
        "verified",
        1,
    ),
    (
        "match_tuple_rest_expression_verified",
        "dot_dot_patterns plain tuple trailing rest match-expression",
        "verified",
        1,
    ),
    (
        "match_tuple_struct_rest_expression_verified",
        "dot_dot_patterns tuple constructor trailing rest match-expression",
        "verified",
        1,
    ),
    (
        "match_literal_arm_wrong_value_counterexample",
        "const_and_literals test3 reachable false literal arm",
        "counterexample",
        1,
    ),
    (
        "match_literal_bool_wrong_branch_counterexample",
        "const_and_literals m_bool_lit false witness",
        "counterexample",
        1,
    ),
    (
        "match_single_arm_enum_wrong_value_counterexample",
        "match_single_arm_issue_444 c_fail subset",
        "counterexample",
        1,
    ),
    (
        "match_struct_rest_false_arm_counterexample",
        "test3_struct_dots_fail struct rest false witness",
        "counterexample",
        1,
    ),
    (
        "match_or_pattern_false_arm_counterexample",
        "test_or_patterns false or-pattern arm witness",
        "counterexample",
        1,
    ),
    (
        "match_or_pattern_with_guard_counterexample",
        "pattern_has_both_or_pat_and_if_guard_issue1208 Rust-semantics false arm",
        "counterexample",
        1,
    ),
    (
        "match_enum_payload_false_branch_counterexample",
        "test1 Maybe::Some payload false branch",
        "counterexample",
        1,
    ),
    (
        "match_tuple_struct_payload_false_branch_counterexample",
        "test3_tuple_struct tuple-struct payload false branch",
        "counterexample",
        1,
    ),
    (
        "match_named_struct_exact_false_branch_counterexample",
        "test3_struct exact struct false branch",
        "counterexample",
        1,
    ),
    (
        "match_literal_fallback_false_branch_counterexample",
        "const_and_literals integer fallback false branch",
        "counterexample",
        1,
    ),
    (
        "match_or_pattern_empty_variant_wrong_branch_counterexample",
        "or_pattern_1_disjunct_issue1588 empty arm false witness",
        "counterexample",
        1,
    ),
    (
        "match_leading_or_pattern_single_variant_counterexample",
        "or_pattern_1_disjunct_issue1588 leading single-disjunct false arm",
        "counterexample",
        1,
    ),
    (
        "match_enum_tuple_variant_statement_payload_error",
        "test3_fails3 Pair::Pair statement-arm payload boundary",
        "error",
        0,
    ),
    (
        "match_guard_order_expression_error",
        "test1 guarded Maybe::Some match expression",
        "error",
        0,
    ),
    (
        "match_or_pattern_with_guard_expression_error",
        "pattern_has_both_or_pat_and_if_guard_issue1208 guard boundary",
        "error",
        0,
    ),
    (
        "match_at_pattern_expression_error",
        "at_patterns nested binding boundary",
        "error",
        0,
    ),
    (
        "match_unreached_call_expression_error",
        "test2_unreached unreachable call boundary",
        "error",
        0,
    ),
    (
        "match_unreached_dead_branch_expression_error",
        "test2_unreached dead unreached arm boundary",
        "error",
        0,
    ),
    (
        "match_boxed_recursive_list_expression_error",
        "test2 List<A> boxed recursive match boundary",
        "error",
        0,
    ),
];

pub fn match_rs_expected_cases() -> &'static [MatchExpectedCase] {
    MATCH_RS_EXPECTED_CASES
}

#[derive(Clone, Copy)]
enum MatchMaybe {
    None,
    Some(u64),
}

#[derive(Clone, Copy)]
enum MatchNestedMaybe {
    None,
    Some(MatchMaybe),
}

#[derive(Clone, Copy)]
enum MatchEither {
    Left(u64),
    Right(u64),
    Empty,
}

#[derive(Clone, Copy)]
enum MatchSingle {
    B,
}

#[derive(Clone, Copy)]
enum MatchHand {
    Left,
    Right,
}

#[derive(Clone, Copy)]
struct MatchPair(u64, u64);

#[derive(Clone, Copy)]
struct MatchBoolPair(bool, bool);

#[derive(Clone, Copy)]
enum MatchBoolEnumPair {
    Pair(bool, bool),
}

#[derive(Clone, Copy)]
enum MatchBoolEnumStructPair {
    Pair { left: bool, right: bool },
}

#[derive(Clone, Copy)]
struct MatchNamedPair {
    left: u64,
    right: u64,
}

#[derive(Clone, Copy)]
struct MatchQuad(u64, bool, u64, u64);

enum MatchGenericMaybe<A> {
    None,
    Some(A),
}

enum MatchBoxList {
    Nil,
    Cons(u64, Box<MatchBoxList>),
}

#[trust_vc::ensures(result == 100u64)]
fn match_payload_binding_value_verified() -> u64 {
    match MatchMaybe::Some(100u64) {
        MatchMaybe::None => 1u64,
        MatchMaybe::Some(hd) => hd,
    }
}

#[trust_vc::ensures(result == 1u64)]
fn match_none_arm_selection_verified() -> u64 {
    match MatchMaybe::None {
        MatchMaybe::None => 1u64,
        MatchMaybe::Some(hd) => hd,
    }
}

#[trust_vc::ensures(result == 0u64)]
fn match_literal_bool_selection_verified() -> u64 {
    match true {
        true => 0u64,
        _ => 20u64,
    }
}

#[trust_vc::ensures(result == 19u64)]
fn match_literal_fallback_value_verified() -> u64 {
    match 19u64 {
        20u64 => 0u64,
        fallback => fallback,
    }
}

#[trust_vc::ensures(result == 0u64)]
fn match_single_arm_enum_verified() -> u64 {
    match MatchSingle::B {
        MatchSingle::B => 0u64,
    }
}

#[trust_vc::ensures(result == 9u64)]
fn match_struct_rest_payload_verified() -> u64 {
    match (MatchNamedPair {
        left: 4u64,
        right: 9u64,
    }) {
        MatchNamedPair { right, .. } => right,
    }
}

#[trust_vc::ensures(result == 8u64)]
fn match_or_pattern_payload_verified() -> u64 {
    match MatchEither::Right(7u64) {
        MatchEither::Left(payload) | MatchEither::Right(payload) => payload + 1u64,
        MatchEither::Empty => 0u64,
    }
}

#[trust_vc::ensures(true)]
fn match_literal_arm_wrong_value_counterexample() {
    match 7u32 {
        7u32 => {
            trust_vc::assert!(false);
        }
        _ => {}
    }
}

#[trust_vc::ensures(true)]
fn match_literal_bool_wrong_branch_counterexample() {
    match true {
        true => {
            trust_vc::assert!(false);
        }
        _ => {}
    }
}

#[trust_vc::ensures(true)]
fn match_single_arm_enum_wrong_value_counterexample() {
    match MatchSingle::B {
        MatchSingle::B => {
            trust_vc::assert!(false);
        }
    }
}

#[trust_vc::ensures(true)]
fn match_struct_rest_false_arm_counterexample() {
    match (MatchNamedPair {
        left: 4u64,
        right: 9u64,
    }) {
        MatchNamedPair { .. } => {
            trust_vc::assert!(false);
        }
    }
}

#[trust_vc::ensures(true)]
fn match_or_pattern_false_arm_counterexample() {
    match MatchEither::Right(7u64) {
        MatchEither::Left(_) | MatchEither::Right(_) => {
            trust_vc::assert!(false);
        }
        MatchEither::Empty => {}
    }
}

#[trust_vc::ensures(result == 13u64)]
fn match_tuple_struct_payload_binding_value_verified() -> u64 {
    match MatchPair(4u64, 9u64) {
        MatchPair(left, right) => left + right,
    }
}

#[trust_vc::ensures(result == 13u64)]
fn match_named_struct_exact_payload_verified() -> u64 {
    match (MatchNamedPair {
        left: 4u64,
        right: 9u64,
    }) {
        MatchNamedPair { left, right } => left + right,
    }
}

#[trust_vc::ensures(result == 3u64)]
fn match_literal_integer_specific_arm_verified() -> u64 {
    match 7u64 {
        5u64 => 1u64,
        7u64 => 3u64,
        _ => 9u64,
    }
}

#[trust_vc::ensures(result == 42u64)]
fn match_or_pattern_empty_variant_verified() -> u64 {
    match MatchEither::Empty {
        MatchEither::Left(payload) | MatchEither::Right(payload) => payload,
        MatchEither::Empty => 42u64,
    }
}

#[trust_vc::ensures(result)]
fn match_enum_tuple_variant_pair_payload_verified() -> bool {
    match MatchBoolEnumPair::Pair(true, false) {
        MatchBoolEnumPair::Pair(left, right) => left && !right,
    }
}

#[trust_vc::ensures(result)]
fn match_enum_struct_variant_payload_verified() -> bool {
    match (MatchBoolEnumStructPair::Pair {
        left: true,
        right: false,
    }) {
        MatchBoolEnumStructPair::Pair { left, right } => left && !right,
    }
}

#[rustfmt::skip]
#[trust_vc::ensures(result == 11u64)]
fn match_leading_or_pattern_single_variant_verified() -> u64 {
    match MatchEither::Left(9u64) {
        | MatchEither::Left(payload) => payload + 2u64,
        _ => 0u64,
    }
}

#[trust_vc::ensures(true)]
fn match_enum_payload_false_branch_counterexample() {
    match MatchMaybe::Some(100u64) {
        MatchMaybe::None => {}
        MatchMaybe::Some(_payload) => {
            trust_vc::assert!(false);
        }
    }
}

#[trust_vc::ensures(true)]
fn match_tuple_struct_payload_false_branch_counterexample() {
    match MatchPair(4u64, 9u64) {
        MatchPair(_left, _right) => {
            trust_vc::assert!(false);
        }
    }
}

#[trust_vc::ensures(true)]
fn match_named_struct_exact_false_branch_counterexample() {
    match (MatchNamedPair {
        left: 4u64,
        right: 9u64,
    }) {
        MatchNamedPair { .. } => {
            trust_vc::assert!(false);
        }
    }
}

#[trust_vc::ensures(true)]
fn match_literal_fallback_false_branch_counterexample() {
    match 19u64 {
        20u64 => {}
        _fallback => {
            trust_vc::assert!(false);
        }
    }
}

#[trust_vc::ensures(true)]
fn match_or_pattern_empty_variant_wrong_branch_counterexample() {
    match MatchEither::Empty {
        MatchEither::Left(_) | MatchEither::Right(_) => {}
        MatchEither::Empty => {
            trust_vc::assert!(false);
        }
    }
}

#[rustfmt::skip]
#[trust_vc::ensures(true)]
fn match_leading_or_pattern_single_variant_counterexample() {
    match MatchEither::Left(9u64) {
        | MatchEither::Left(_) => {
            trust_vc::assert!(false);
        }
        _ => {}
    }
}

#[trust_vc::ensures(true)]
fn match_enum_tuple_variant_statement_payload_error() {
    match MatchBoolEnumPair::Pair(true, false) {
        MatchBoolEnumPair::Pair(_left, right) => {
            trust_vc::assert!(right);
        }
    }
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding rework): a tuple-struct
// local destructure `let MatchBoolPair(left, right) = pair` now binds and
// verifies; discriminator-certified genuine by two model-backed probes
// (`assert!(!left)` and `assert!(right)` falsified variants both
// Counterexample).
#[trust_vc::ensures(true)]
fn match_tuple_struct_local_destructure_verified() {
    let pair = MatchBoolPair(true, false);
    let MatchBoolPair(left, right) = pair;
    trust_vc::assert!(left);
    trust_vc::assert!(!right);
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding rework): a single-variant
// enum tuple local destructure `let MatchBoolEnumPair::Pair(left, right) =
// pair` now binds and verifies. Newly unmasked behind the tuple-struct row's
// suite short-circuit; stash-controlled pre-existing and discriminator-
// certified genuine by two model-backed probes (`assert!(!left)` and
// `assert!(right)` falsified variants both Counterexample at their own
// obligation).
#[trust_vc::ensures(true)]
fn match_enum_tuple_variant_local_destructure_verified() {
    let pair = MatchBoolEnumPair::Pair(true, false);
    let MatchBoolEnumPair::Pair(left, right) = pair;
    trust_vc::assert!(left);
    trust_vc::assert!(!right);
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding rework): tuple-struct rest
// destructures `MatchQuad(first, .., last)` / `MatchQuad(.., flag, third,
// fourth)` now bind with exact suffix/prefix alignment. Newly unmasked by the
// fail-closed list's suite short-circuit; stash-controlled pre-existing and
// discriminator-certified genuine by three probes (`first == 2`, `third == 4`,
// and the misalignment discriminator `last == 1` all Counterexample at their
// own obligation).
#[trust_vc::ensures(true)]
fn match_tuple_struct_rest_local_destructure_verified() {
    let quad = MatchQuad(1u64, false, 3u64, 4u64);
    let MatchQuad(first, .., last) = quad;
    trust_vc::assert!(first == 1u64);
    trust_vc::assert!(last == 4u64);

    let MatchQuad(.., flag, third, fourth) = quad;
    trust_vc::assert!(!flag);
    trust_vc::assert!(third == 3u64);
    trust_vc::assert!(fourth == 4u64);
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding rework): a struct rest
// destructure `MatchNamedPair { right, .. }` now binds and verifies. Newly
// unmasked (suite short-circuit); stash-controlled pre-existing and
// discriminator-certified genuine (falsified assert AND falsified constructed
// value both Counterexample; renamed-binder `right: renamed_right` variant
// verifies).
#[trust_vc::ensures(true)]
fn match_struct_rest_local_destructure_verified() {
    let pair = MatchNamedPair {
        left: 4u64,
        right: 9u64,
    };
    let MatchNamedPair { right, .. } = pair;
    trust_vc::assert!(right == 9u64);
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding rework): an exact struct
// destructure `MatchNamedPair { left, right }` now binds and verifies. Newly
// unmasked (suite short-circuit); stash-controlled pre-existing and
// discriminator-certified genuine (`left == 5` and `right == 8` falsified
// variants both Counterexample at their own obligation).
#[trust_vc::ensures(true)]
fn match_struct_exact_local_destructure_verified() {
    let pair = MatchNamedPair {
        left: 4u64,
        right: 9u64,
    };
    let MatchNamedPair { left, right } = pair;
    trust_vc::assert!(left == 4u64);
    trust_vc::assert!(right == 9u64);
}

// De-surrogated (Phase E match sub-lane): a plain-tuple pattern in
// match-EXPRESSION position `match (a, b) { (left, right) => <body> }` now lowers
// and verifies through the single-variant "Tuple" datatype + Constructor
// machinery — left/right project to the tuple selectors Tuple_0/Tuple_1, NOT
// havoc. This mirrors the verified tuple-struct sibling
// `match_enum_tuple_variant_pair_payload_verified` and upstream test4's
// `(true, false)` shape. Discriminator-certified genuine: the false-payload
// `(left, right) => left && right` (true && false == false) Counterexamples
// against `ensures(result)`.
//
// A pure-value (boolean) body is used deliberately: an ARITHMETIC body
// (`left + right`) additionally emits an exec overflow obligation whose
// tuple-projection binding lives in body_extract's scoped-value string projector
// (out of this lane's scope), so it stays fail-closed. See the engine soundness
// gate `match_plain_tuple_expression_soundness` for the pinned boundary.
#[trust_vc::ensures(result)]
fn match_plain_tuple_pattern_expression_verified() -> bool {
    match (true, false) {
        (left, right) => left && !right,
    }
}

// De-surrogated 2026-07-18 (ROOT-D pattern-binding rework): a plain tuple
// local `let (left, _right) = (true, false)` now binds and verifies;
// discriminator-certified genuine ((false, true) swap Counterexamples).
#[trust_vc::ensures(result)]
fn match_plain_tuple_local_pattern_verified() -> bool {
    let (left, _right) = (true, false);
    left
}

// De-surrogated (Phase E match sub-lane): a TRAILING `..` rest in a plain-tuple
// pattern in match-EXPRESSION position `match (a, ..) { (first, ..) => first }`
// now lowers through the single-variant "Tuple" datatype + Constructor
// `has_rest` machinery (mirroring the sound struct-rest path): `first` projects
// to the tuple selector `Tuple_0` and the trailing fields are IGNORED — no
// havoc. Discriminator-certified genuine by the adversarial engine gate
// `match_rest_pattern_expression_soundness` (false-payload `result == <field-1
// value>` and ignored-field `result == <rest field value>` both
// Counterexample). A value body (`first`) is used deliberately: an ARITHMETIC
// body (`first + last`) additionally needs the exec overflow obligation to bind
// the projection in body_extract's string projector (out of this lane's scope,
// like the plain-tuple sibling). A MIDDLE/back rest (`(first, .., last)`, a
// binding after `..`) stays fail-closed — see the engine gate.
#[trust_vc::ensures(result == 1u64)]
fn match_tuple_rest_expression_verified() -> u64 {
    match (1u64, false, 3u64, 4u64) {
        (first, ..) => first,
    }
}

#[trust_vc::ensures(result == 104u64)]
fn match_guard_order_expression_error() -> u64 {
    match MatchMaybe::Some(100u64) {
        MatchMaybe::None => 1u64,
        MatchMaybe::Some(n) if n < 10u64 => n + 2u64,
        MatchMaybe::Some(n) if n < 100u64 => n + 3u64,
        MatchMaybe::Some(n) if n < 200u64 => n + 4u64,
        MatchMaybe::Some(n) => n + 5u64,
    }
}

#[trust_vc::ensures(result == 0u64)]
fn match_or_pattern_with_guard_expression_error() -> u64 {
    match MatchMaybe::Some(1u64) {
        MatchMaybe::None | MatchMaybe::Some(_) if true => 0u64,
        _ => 1u64,
    }
}

#[trust_vc::ensures(result)]
fn match_range_pattern_expression_verified() -> bool {
    match 4u64 {
        3u64..=5u64 => true,
        _ => false,
    }
}

#[trust_vc::ensures(result == 100u64)]
fn match_at_pattern_expression_error() -> u64 {
    match MatchNestedMaybe::Some(MatchMaybe::Some(100u64)) {
        MatchNestedMaybe::Some(_inner @ MatchMaybe::Some(payload)) => payload,
        _ => 0u64,
    }
}

// De-surrogated (Phase E match sub-lane): a TRAILING `..` rest in a tuple-struct
// pattern in match-EXPRESSION position `match x { MatchQuad(first, ..) => first }`
// now lowers through the Constructor `has_rest` machinery (mirroring the sound
// struct-rest path): `first` projects to the field-0 selector `MatchQuad_0` and
// the trailing fields (including the `bool`) are IGNORED — no havoc.
// Discriminator-certified genuine by the adversarial engine gate
// `match_rest_pattern_expression_soundness` (false-payload and ignored-field
// both Counterexample). A MIDDLE/back rest (`MatchQuad(first, .., last)`, a
// binding after `..`) stays fail-closed.
#[trust_vc::ensures(result == 1u64)]
fn match_tuple_struct_rest_expression_verified() -> u64 {
    match MatchQuad(1u64, false, 3u64, 4u64) {
        MatchQuad(first, ..) => first,
    }
}

#[trust_vc::ensures(result == 100u64)]
fn match_if_let_expression_verified() -> u64 {
    if let MatchMaybe::Some(payload) = MatchMaybe::Some(100u64) {
        payload
    } else {
        0u64
    }
}

#[trust_vc::ensures(result == 10u64)]
fn match_unreached_call_expression_error() -> u64 {
    match MatchHand::Right {
        MatchHand::Left => 10u64,
        MatchHand::Right => unreachable!(),
    }
}

#[trust_vc::ensures(result == 10u64)]
fn match_unreached_dead_branch_expression_error() -> u64 {
    match MatchHand::Left {
        MatchHand::Left => 10u64,
        MatchHand::Right => unreachable!(),
    }
}

#[trust_vc::ensures(true)]
fn match_or_pattern_with_guard_counterexample() {
    match (true, false) {
        (true, a) | (a, false) if a => {
            trust_vc::assert!(false);
        }
        _ => {}
    }
}

// De-surrogated 2026-07-18: a generic-enum match expression at a CONCRETE
// instantiation (`MatchGenericMaybe::Some(11u64)`) now verifies through the
// per-instantiation datatype carrier. Newly unmasked (suite short-circuit);
// stash-controlled pre-existing and discriminator-certified genuine
// (`ensures(result == 12u64)` and constructed `Some(12u64)` against
// `ensures(result == 11u64)` both Counterexample at the postcondition).
#[trust_vc::ensures(result == 11u64)]
fn match_generic_enum_expression_verified() -> u64 {
    match MatchGenericMaybe::Some(11u64) {
        MatchGenericMaybe::None => 0u64,
        MatchGenericMaybe::Some(payload) => payload,
    }
}

#[trust_vc::ensures(result == 0u64)]
fn match_boxed_recursive_list_expression_error(list: MatchBoxList) -> u64 {
    match list {
        MatchBoxList::Nil => 0u64,
        MatchBoxList::Cons(head, _tail) => head,
    }
}

#[trust_vc::proof]
#[trust_vc::ensures(result == 1u64)]
fn match_proof_guard_statement_verified() -> u64 {
    match MatchMaybe::Some(1u64) {
        MatchMaybe::Some(payload) if payload == 1u64 => 1u64,
        _ => 0u64,
    }
}

#[trust_vc::spec]
#[trust_vc::ensures(result)]
fn match_spec_range_expression_verified() -> bool {
    match 4u64 {
        3u64..=5u64 => true,
        _ => false,
    }
}
