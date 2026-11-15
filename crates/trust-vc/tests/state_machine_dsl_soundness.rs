// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness harness for the D1a `state_machine!` expansion.
//!
//! Four batteries, each with its own failure mode in view:
//!
//! * CONTROLS (`fixtures/state_machine/sm_controls.rs`) — every generated
//!   relation, frame, branch, `next` and inductiveness lemma that D1a claims,
//!   plus a SATISFIABILITY WITNESS per transition and per init. A witness is
//!   what makes "the lemma verified" meaningful: an always-false relation
//!   would discharge every inductiveness obligation vacuously, and the witness
//!   pairs catch exactly that.
//! * LIARS (`sm_liars.rs`) — one token away from a control each, including one
//!   per branch path, the implicit-else continuation, the dropped require, the
//!   let substitution, and witness twins with a wrong post field. None may
//!   ever be `Verified`.
//! * GATED (`sm_refusals.rs`, the shadow fixtures) — every refusal fails
//!   closed through a client function with its pinned message.
//! * ENGINE SEAM (`sm_engine_seam.rs`) — a generated definition whose body
//!   axiom the engine would drop is a hard error, not a silent uninterpreted
//!   function.
//!
//! The LEMMA-CONJUNCTION rule is pinned here too: a case that references a
//! machine counts only if every generated INIT/IND lemma of that machine
//! verifies. Lemma ensures are assumed MODULARLY at call sites, so a client of
//! a machine whose lemma is false verifies on its own — `calls_the_false_lemma`
//! in `sm_liars.rs` is the measured proof of that, and the rule is what keeps
//! it from being credited.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use trust_vc_core::{state_machine_dsl, verify_function_from_file, VerifyResult};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/state_machine")
        .join(name)
}

fn fixture_str(name: &str) -> String {
    fixture(name)
        .to_str()
        .expect("fixture path should be UTF-8")
        .to_string()
}

fn verify(path: &str, case: &str) -> VerifyResult {
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract from {path}: {err}"))
}

/// Cases that must be `Verified`.
const CONTROLS: &[&str] = &[
    // (a)/(k) transition relations and their inductiveness lemmas
    "ctl_initialize_inductive",
    "ctl_tr1_inductive",
    "ctl_tr2_inductive",
    // (d) the frame and the effect
    "ctl_frame",
    "ctl_tr1_effect",
    // (b) the upstream `initialize` if/else init
    "ctl_init_branch",
    "ctl_init_same_branch",
    // (g) the readonly frame
    "ctl_readonly_frame",
    // (e) `next` elimination and introduction
    "ctl_next_elim",
    "ctl_next_intro",
    // (k) require-after-update, both paths
    "ctl_tr2_effect",
    "ctl_tr2_else_effect",
    // `_enabled` without the postconditions
    "ctl_enabled",
    // satisfiability witnesses
    "ctl_witness_tr1",
    "ctl_witness_tr2",
    "ctl_witness_initialize",
    "ctl_witness_r",
    // (c) a lemma body that calls a file-root helper lemma
    "hlp_scale_inductive",
    "hlp_witness_scale",
    // (f) datatype fields, derived-PartialEq and no-PartialEq
    "dt_start_inductive",
    "dt_busy_inductive",
    "dt_setc_inductive",
    "dt_busy_effect",
    "dt_setc_effect",
    "dt_witness_busy",
    "dt_witness_start",
    // (j) a `nat` parameter carries its range fact
    "natp_monotone",
    "natp_next_monotone",
    "natp_witness_addk",
    // (i) no invariant: `invariant()` is `true`
    "noinv_true_invariant",
    // (h) two machines plus a user `State` with its own `invariant`
    "two_tr1_inductive",
    "two_tr1_effect",
    "two_invariants_are_distinct",
    "user_state_is_untouched",
    "two_witness_tr1",
    // a file-root helper lemma is an ordinary proof fn
    "helper_mul_ge",
];

/// The expected NON-verified verdict class of each liar.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Liar {
    /// A ground refutation.
    Counterexample,
    /// Not discharged, with no model (solver incompleteness). A FAILURE
    /// verdict, but not a counterexample: recorded, and kept out of the
    /// manifest's counterexample set.
    NotProved,
    /// The premises are contradictory, so nothing was proved.
    Vacuous,
}

const LIARS: &[(&str, Liar)] = &[
    // (a') a transition that breaks the invariant
    ("liar_tr1_inductive", Liar::Counterexample),
    // (b') per-path init liar; (b'') the same without a binder
    ("liar_initialize_inductive", Liar::NotProved),
    ("liar_initialize2_inductive", Liar::Counterexample),
    // (e') the implicit-else continuation
    ("liar_implicit_else_inductive", Liar::Counterexample),
    // (p1)/(p2) one path breaks the invariant
    ("liar_path_inductive", Liar::Counterexample),
    // (i') the let substitution
    ("letsub_liar", Liar::Counterexample),
    // (d') the frame
    ("ctl2_frame_liar", Liar::Counterexample),
    // (d'') the then-branch effect under the else condition
    ("ctl2_branch_liar", Liar::Counterexample),
    // (h') the dropped require
    ("ctl2_dropped_require_liar", Liar::Counterexample),
    // (w') a witness twin with one post field wrong
    ("ctl2_witness_liar", Liar::Counterexample),
    // the readonly frame
    ("ctl2_readonly_liar", Liar::Counterexample),
    // (n') a `next` introduction needing a negative `nat`
    ("natp2_negative_witness_liar", Liar::Counterexample),
    // (q') cross-machine invariant confusion
    ("crosstalk_liar", Liar::Counterexample),
    // twins of the three controls under which ay logs a REJECTED UNSAT
    // certificate and publishes the result anyway (see `sm_liars.rs`; the
    // behaviour is PRE-EXISTING and reproduces at HEAD on hand-written Rust
    // with no `state_machine!`). These are what would turn red if such a
    // published-but-uncertified UNSAT ever became a false `Verified`.
    // MEASURED: the lemma liar is an incompleteness (the invariant `v <= 10`
    // against `v * k` needs quantified reasoning), so the GROUND twin below
    // carries the refutation.
    ("liarcert_scale_inductive", Liar::NotProved),
    ("liarcert_scale_effect_liar", Liar::Counterexample),
    ("liarcert_natp_strict_liar", Liar::Counterexample),
    ("liarcert_user_state_liar", Liar::Counterexample),
    // (j') a lemma body that assumes `false`
    ("assume_false_inductive", Liar::Vacuous),
    // the false lemma itself (its CLIENT verifies modularly — see the
    // lemma-conjunction rule below)
    ("false_lemma_inductive", Liar::Counterexample),
];

/// Liar-file cases that must still be `Verified`: each is the other half of a
/// discriminator pair.
const LIAR_FILE_CONTROLS: &[&str] = &[
    "path_then_branch_is_sound",
    "letsub_control",
    "ctl2_dropped_require_control",
    "liarcert_scale_effect_control",
    "liarcert_user_state_control",
];

/// Liar-file cases that VERIFY but may never be counted as evidence, because
/// they reference a machine whose inductiveness lemma is refuted. Both are
/// measured facts about MODULAR trust, not accidents:
/// `path_then_branch_is_sound` is true of one path of a relation whose lemma
/// fails on the other, and `calls_the_false_lemma` verifies only because a
/// lemma's ensures is assumed at its call site.
/// `liarcert_scale_effect_control` joins them for the same reason: it is a
/// true, ground fact about `LiarCert::scale`, whose INVARIANT lemma is a liar.
const MODULAR_TRUST_ONLY: &[&str] = &[
    "path_then_branch_is_sound",
    "calls_the_false_lemma",
    "liarcert_scale_effect_control",
];

const GATED: &[(&str, &str, &[&str])] = &[
    ("sm_refusals.rs", "gate_nat_field", &["field `t` has type `nat`; nat-typed state fields carry no range fact"]),
    ("sm_refusals.rs", "gate_u32_field", &["field `t` has machine-integer type `u32`"]),
    ("sm_refusals.rs", "gate_usize_field", &["field `t` has machine-integer type `usize`"]),
    ("sm_refusals.rs", "gate_f64_field", &["field `t` has type `f64`, which is not a file-local datatype admitted by D1a"]),
    ("sm_refusals.rs", "gate_seq_field", &["field `t` has collection type `Seq<int>`; collection-valued fields need extensional equality"]),
    ("sm_refusals.rs", "gate_map_field", &["collection type `Map<int , int>`"]),
    ("sm_refusals.rs", "gate_manual_eq_field", &["field `t` has type `Liar`, which is not a file-local datatype admitted by D1a"]),
    ("sm_refusals.rs", "gate_manual_eq_via_holder", &["field `t` has type `Holder`, which is not a file-local datatype admitted by D1a"]),
    ("sm_refusals.rs", "gate_recursive_field", &["field `t` has type `Rec`"]),
    ("sm_refusals.rs", "gate_generic_field", &["field `t` has type `Gen`"]),
    ("sm_refusals.rs", "gate_float_bearing_field", &["field `t` has type `Floaty`"]),
    ("sm_refusals.rs", "gate_assert", &["`assert` in a transition is not yet supported"]),
    ("sm_refusals.rs", "gate_match", &["`match` in a transition is not yet supported"]),
    ("sm_refusals.rs", "gate_property", &["`property!` is not yet supported"]),
    ("sm_refusals.rs", "gate_require_let", &["`require let` / `assert let` are not yet supported"]),
    ("sm_refusals.rs", "gate_birds_eye", &["`birds_eye` only makes sense for tokenized state machines"]),
    ("sm_refusals.rs", "gate_sharding_op", &["'add' statement not allowed for field with sharding strategy 'variable'"]),
    ("sm_refusals.rs", "gate_sub_update", &["sub-field/index `update t…` is not yet supported"]),
    ("sm_refusals.rs", "gate_division", &["expression form `pre . t / 2` is not supported in a D1a transition body"]),
    ("sm_refusals.rs", "gate_cast", &["expression form `x as int` is not supported"]),
    ("sm_refusals.rs", "gate_bare_pre", &["`pre` may only be used as `pre.<field>`"]),
    ("sm_refusals.rs", "gate_unknown_call", &["call to `unknown_helper` is not supported"]),
    ("sm_refusals.rs", "gate_lemma_requires_false", &["[trust_vc :: requires (false)]", "is not allowed on an inductive lemma"]),
    ("sm_refusals.rs", "gate_lemma_satisfiable_requires", &["is not allowed on an inductive lemma"]),
    ("sm_refusals.rs", "gate_lemma_external_body", &["external_body", "is not allowed on an inductive lemma"]),
    ("sm_refusals.rs", "gate_lemma_verifier_external_body", &["verifier :: external_body", "is not allowed on an inductive lemma"]),
    ("sm_refusals.rs", "gate_lemma_cfg_attr", &["cfg_attr", "is not allowed on an inductive lemma"]),
    ("sm_refusals.rs", "gate_lemma_requires_macro", &["requires!/ensures!/recommends!/decreases! inside an inductive lemma body are not allowed"]),
    ("sm_refusals.rs", "gate_invariant_attr", &["is not allowed on an invariant fn"]),
    ("sm_refusals.rs", "gate_invariant_statements", &["invariant `inv` body must be a single expression"]),
    ("sm_refusals.rs", "gate_helper_fn", &["helper fn `helper` inside state_machine! is not yet supported"]),
    ("sm_refusals.rs", "gate_label", &["transition labels (`Label`/`InitLabel`) are not yet supported"]),
    ("sm_refusals.rs", "gate_pre_param", &["`pre` is reserved (pre/post/self/Self)"]),
    ("sm_refusals.rs", "gate_generated_prefix", &["generated item `__TvcSm_x` collides with an existing item"]),
    ("sm_refusals.rs", "gate_tokenized", &["tokenized_state_machine! is not yet supported"]),
    ("sm_refusals.rs", "gate_step_path", &["`Ok1::Step` is not generated by D1a state_machine!"]),
    ("sm_refusals.rs", "gate_show_path", &["`Ok1::show::tr` is not generated by D1a state_machine!"]),
    ("sm_refusals.rs", "gate_ufcs_invariant", &["call `.invariant()` with method syntax"]),
    ("sm_refusals.rs", "gate_next_by", &["`Ok1::State::next_by` is not generated by D1a state_machine!"]),
    (
        "sm_shadow_use_import.rs",
        "shadow_use_import_client",
        &["bare state_machine! is not resolved to trust_vc here; write `trust_vc::state_machine!`"],
    ),
    (
        "sm_shadow_rebound_root.rs",
        "shadow_rebound_root_client",
        &["state_machine! via `trust_vc::state_machine` is not trust_vc's macro and is not verified"],
    ),
    (
        "sm_bare_unbound.rs",
        "bare_unbound_client",
        &["bare state_machine! is not resolved to trust_vc here"],
    ),
    (
        "sm_tokenized_item.rs",
        "tokenized_item_client",
        &["tokenized_state_machine! is not yet supported"],
    ),
    (
        "sm_foreign_macro.rs",
        "foreign_machine_client",
        &["state_machine! via `other_dsl::state_machine` is not trust_vc's macro and is not verified"],
    ),
    (
        "sm_refusals.rs",
        "gate_indirect_reference",
        &["__trust_vc_sm_poison_"],
    ),
    (
        "sm_engine_seam.rs",
        "seam_relation_axiom_dropped",
        &["generated state_machine! definition `__TvcSm_Seam__tr` has no definitional axiom; refusing to treat it as uninterpreted"],
    ),
    (
        "sm_engine_seam.rs",
        "seam_invariant_axiom_dropped",
        &["generated state_machine! definition `__TvcSm_Seam_State::invariant` has no definitional axiom"],
    ),
];

#[test]
fn controls_verify() {
    let path = fixture_str("sm_controls.rs");
    for case in CONTROLS {
        let result = verify(&path, case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "control {case} must verify, got: {result:?}"
        );
    }
}

#[test]
fn liars_never_verify() {
    let path = fixture_str("sm_liars.rs");
    for (case, expected) in LIARS {
        let result = verify(&path, case);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "liar {case} must never verify, got: {result:?}"
        );
        let observed = match &result {
            VerifyResult::Counterexample { .. } => Liar::Counterexample,
            VerifyResult::NotProved { .. } => Liar::NotProved,
            VerifyResult::Unknown { .. } => Liar::Vacuous,
            other => panic!("liar {case} produced an unexpected verdict: {other:?}"),
        };
        assert_eq!(
            observed, *expected,
            "liar {case} changed verdict class: {result:?}"
        );
    }
}

#[test]
fn the_other_half_of_each_discriminator_pair_still_verifies() {
    let path = fixture_str("sm_liars.rs");
    for case in LIAR_FILE_CONTROLS {
        let result = verify(&path, case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} must verify, got: {result:?}"
        );
    }
}

#[test]
fn a_client_of_a_false_lemma_verifies_modularly() {
    // MEASURED, and the reason the lemma-conjunction rule exists: a lemma's
    // ensures is ASSUMED at its call site, so this client is `Verified` even
    // though the lemma it calls is refuted.
    let path = fixture_str("sm_liars.rs");
    assert!(matches!(
        verify(&path, "calls_the_false_lemma"),
        VerifyResult::Verified
    ));
    assert!(matches!(
        verify(&path, "false_lemma_inductive"),
        VerifyResult::Counterexample { .. }
    ));
}

#[test]
fn gated_cases_fail_closed_with_their_pinned_message() {
    for (file, case, fragments) in GATED {
        let path = fixture_str(file);
        let message = match verify_function_from_file(&path, case) {
            Err(err) => err.to_string(),
            Ok(VerifyResult::Error { message }) => message,
            Ok(other) => panic!("{case} ({file}) must fail closed, got: {other:?}"),
        };
        assert!(
            message.contains("state_machine!") || message.contains("__trust_vc_sm_poison_"),
            "{case} ({file}) message should name the macro or its poison: {message}"
        );
        for fragment in *fragments {
            assert!(
                message.contains(fragment),
                "{case} ({file}) should contain {fragment:?}, got: {message}"
            );
        }
    }
}

#[test]
fn a_refused_sibling_does_not_take_the_file_down() {
    let path = fixture_str("sm_refusals.rs");
    assert!(matches!(
        verify(&path, "refusals_file_still_verifies_ok1"),
        VerifyResult::Verified
    ));
    let seam = fixture_str("sm_engine_seam.rs");
    assert!(matches!(
        verify(&seam, "seam_unmarked_control"),
        VerifyResult::Verified
    ));
}

#[test]
fn a_file_local_macro_rules_invocation_keeps_head_behaviour() {
    let path = fixture_str("sm_shadow_inline_mod_macro_rules.rs");
    let source = std::fs::read_to_string(&path).expect("fixture readable");
    let mut file = syn::parse_file(&source).expect("fixture parses");
    let before = quote_string(&file);
    state_machine_dsl::expand_file(&mut file);
    assert_eq!(before, quote_string(&file), "the file must be untouched");
    assert!(state_machine_dsl::refusals(&file).is_empty());
    assert!(matches!(
        verify(&path, "shadow_local_macro_rules_client"),
        VerifyResult::Verified
    ));
}

fn quote_string(file: &syn::File) -> String {
    quote::ToTokens::to_token_stream(file).to_string()
}

/// A third-party item macro named `state_machine` is poisoned, and its file
/// refuses every `Verified` answer.
///
/// D1a keys admission on the last path segment, so `other_dsl::state_machine!`
/// — a macro trust-vc does not own and cannot see through — is refused rather
/// than ignored, and the client that references the refused machine fails
/// closed with that refusal (asserted by `GATED` above). Its expansion can also
/// emit an impl, a trait or a type that no reading of the file shows, so the
/// unread-item rule refuses a `Verified` answer for the unrelated functions
/// too. A refutation is kept.
#[test]
fn a_foreign_macro_named_state_machine_is_refused_and_refuses_its_file() {
    let path = fixture_str("sm_foreign_macro.rs");
    let control = verify(&path, "foreign_untouched_control");
    assert!(
        matches!(&control, VerifyResult::Error { message } if message.starts_with("unread item")),
        "an unrelated function must be refused by the unread-item rule, got {control:?}"
    );
    assert!(
        matches!(
            verify(&path, "foreign_untouched_liar"),
            VerifyResult::Counterexample { .. }
        ),
        "an unrelated function must keep HEAD's refutation"
    );

    let source = std::fs::read_to_string(fixture("sm_foreign_macro.rs")).expect("fixture readable");
    let expanded =
        trust_vc_core::parse_file_allow_tracked(&source).expect("fixture parses expanded");
    let refusals = state_machine_dsl::refusals(&expanded);
    let invocation_line = source
        .lines()
        .position(|line| line.starts_with("other_dsl::state_machine!"))
        .expect("the fixture invokes the foreign macro at the file root")
        + 1;
    assert!(
        !refusals.is_empty(),
        "the foreign macro must be refused, not ignored"
    );
    assert_eq!(
        refusals[0].0, invocation_line,
        "the first refusal should sit on the invocation line: {refusals:?}"
    );
    for (_, message) in &refusals {
        assert!(
            message
                .contains("state_machine! via `other_dsl::state_machine` is not trust_vc's macro"),
            "every refusal should carry the foreign-path reason: {message}"
        );
    }
    // One marker for the invocation, one per reference site — here the single
    // `Widget::State` client. The unrelated functions add none.
    assert_eq!(
        refusals.len(),
        2,
        "the invocation and its one reference should each carry a marker: {refusals:?}"
    );
}

/// Mentioning the words in a doc comment, a string or ANOTHER macro's tokens
/// is not an invocation: `expand_file` stays an exact no-op.
#[test]
fn merely_naming_state_machine_in_text_changes_nothing() {
    let source = r#"
/// A doc comment about state_machine! and X::State::tr.
pub fn documented() {}

pub fn mentions() -> &'static str {
    "state_machine! { X { fields { pub t: int } } }"
}

other_macro! { state_machine X::State::tr }
"#;
    let mut file = syn::parse_file(source).expect("the mention-only file parses");
    let before = quote_string(&file);
    state_machine_dsl::expand_file(&mut file);
    assert_eq!(
        before,
        quote_string(&file),
        "a file that only NAMES state_machine must come back byte-identical"
    );
    assert!(state_machine_dsl::refusals(&file).is_empty());
}

/// Every refused or poisoned invocation leaves a marker the CLI reports.
#[test]
fn every_gated_fixture_reports_refusals_at_file_level() {
    for file in [
        "sm_refusals.rs",
        "sm_shadow_use_import.rs",
        "sm_shadow_rebound_root.rs",
        "sm_bare_unbound.rs",
        "sm_tokenized_item.rs",
        "sm_foreign_macro.rs",
    ] {
        let source = std::fs::read_to_string(fixture(file)).expect("fixture readable");
        let expanded =
            trust_vc_core::parse_file_allow_tracked(&source).expect("fixture parses expanded");
        let refusals = state_machine_dsl::refusals(&expanded);
        assert!(
            !refusals.is_empty(),
            "{file} should report at least one refusal"
        );
        for (line, message) in &refusals {
            assert!(*line >= 1, "{file} refusal line should be 1-based");
            assert!(
                message.starts_with("state_machine! `"),
                "{file} refusal should carry the prefix: {message}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// The lemma-conjunction rule.

/// Machines referenced by `case`'s tokens in the RAW fixture.
fn machines_referenced(
    file: &syn::File,
    case: &str,
    machines: &BTreeSet<String>,
) -> BTreeSet<String> {
    fn walk(items: &[syn::Item], case: &str, out: &mut Option<proc_macro2::TokenStream>) {
        for item in items {
            match item {
                syn::Item::Fn(f) if f.sig.ident == case => {
                    *out = Some(quote::ToTokens::to_token_stream(f));
                }
                syn::Item::Mod(m) => {
                    if let Some((_, inner)) = &m.content {
                        walk(inner, case, out);
                    }
                }
                _ => {}
            }
        }
    }
    fn idents(tokens: proc_macro2::TokenStream, out: &mut BTreeSet<String>) {
        for tree in tokens {
            match tree {
                proc_macro2::TokenTree::Ident(ident) => {
                    out.insert(ident.to_string());
                }
                proc_macro2::TokenTree::Group(g) => idents(g.stream(), out),
                _ => {}
            }
        }
    }
    let mut tokens = None;
    walk(&file.items, case, &mut tokens);
    let mut names = BTreeSet::new();
    if let Some(tokens) = tokens {
        idents(tokens, &mut names);
    }
    names.intersection(machines).cloned().collect()
}

/// A case counts as VERIFIED evidence for a machine only if every generated
/// INIT/IND lemma of that machine verifies. Lemma ensures are assumed at call
/// sites, so a machine that is not inductive can otherwise be credited by a
/// client that never fails.
#[test]
fn a_verified_case_only_counts_when_all_of_its_machines_lemmas_verify() {
    let path = fixture_str("sm_controls.rs");
    let source = std::fs::read_to_string(&path).expect("fixture readable");
    let raw = syn::parse_file(&source).expect("fixture parses");
    let lemmas = state_machine_dsl::machine_lemmas(&raw);
    assert!(!lemmas.is_empty(), "the controls fixture declares machines");

    let mut by_machine: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (machine, lemma, kind) in &lemmas {
        assert!(
            matches!(*kind, "init" | "transition"),
            "unexpected lemma kind {kind}"
        );
        by_machine
            .entry(machine.clone())
            .or_default()
            .push(lemma.clone());
    }
    let machines: BTreeSet<String> = by_machine.keys().cloned().collect();
    let controls: BTreeSet<&str> = CONTROLS.iter().copied().collect();

    // Every lemma of every machine is itself a control.
    for (machine, machine_lemmas) in &by_machine {
        for lemma in machine_lemmas {
            assert!(
                controls.contains(lemma.as_str()),
                "lemma {lemma} of machine {machine} is not listed as a control"
            );
        }
    }

    // And every control that references a machine is covered by them.
    for case in CONTROLS {
        for machine in machines_referenced(&raw, case, &machines) {
            for lemma in &by_machine[&machine] {
                assert!(
                    controls.contains(lemma.as_str()),
                    "control {case} references machine {machine}, whose lemma {lemma} is not a control"
                );
                let result = verify(&path, lemma);
                assert!(
                    matches!(result, VerifyResult::Verified),
                    "control {case} references machine {machine}, whose lemma {lemma} does not verify: {result:?}"
                );
            }
        }
    }
}

/// The liar fixture's machines must NOT be creditable: each machine with a
/// failing lemma has no verified client listed as evidence.
#[test]
fn a_machine_with_a_failing_lemma_credits_nothing() {
    let path = fixture_str("sm_liars.rs");
    let source = std::fs::read_to_string(&path).expect("fixture readable");
    let raw = syn::parse_file(&source).expect("fixture parses");
    let lemmas = state_machine_dsl::machine_lemmas(&raw);
    let liars: BTreeSet<&str> = LIARS.iter().map(|(case, _)| *case).collect();
    let machines: BTreeSet<String> = lemmas.iter().map(|(m, _, _)| m.clone()).collect();

    let mut failing_machines = BTreeSet::new();
    for (machine, lemma, _) in &lemmas {
        if liars.contains(lemma.as_str()) {
            failing_machines.insert(machine.clone());
        }
    }
    assert!(
        !failing_machines.is_empty(),
        "the liar fixture should declare machines whose lemmas fail"
    );
    for case in LIAR_FILE_CONTROLS
        .iter()
        .chain(std::iter::once(&"calls_the_false_lemma"))
    {
        let referenced = machines_referenced(&raw, case, &machines);
        let touches_failing = referenced
            .iter()
            .any(|machine| failing_machines.contains(machine));
        if touches_failing {
            assert!(
                MODULAR_TRUST_ONLY.contains(case),
                "{case} verifies and references a machine whose lemma fails, so it must be \
                 recorded as modular-trust-only and never counted as evidence"
            );
        } else {
            assert!(
                !MODULAR_TRUST_ONLY.contains(case),
                "{case} no longer references a failing machine; take it out of MODULAR_TRUST_ONLY"
            );
        }
    }
    // The modular-trust client really does reference the failing machine.
    let referenced = machines_referenced(&raw, "calls_the_false_lemma", &machines);
    assert!(
        referenced.contains("FalseLemma"),
        "the modular-trust client should reference the failing machine"
    );
}

/// The SHAPE of this harness, pinned so a report cannot quote it wrong.
///
/// A ledger row that says "N witnesses, M lemmas" is a claim about the
/// batteries below, and the one written for this increment got both numbers
/// wrong in the same direction. The composition is now derived here: the
/// generated-lemma count comes from `machine_lemmas` over the fixture itself,
/// not from a hand count, so adding a machine without its lemma control — or
/// a transition without its satisfiability witness — fails.
#[test]
fn the_controls_battery_has_the_composition_the_ledger_reports() {
    assert_eq!(CONTROLS.len(), 36, "control count");
    assert_eq!(LIARS.len(), 19, "liar count");
    assert_eq!(LIAR_FILE_CONTROLS.len(), 5, "discriminator-partner count");
    assert_eq!(MODULAR_TRUST_ONLY.len(), 3, "modular-trust-only count");
    assert_eq!(GATED.len(), 47, "gated count");

    let counterexamples = LIARS
        .iter()
        .filter(|(_, class)| *class == Liar::Counterexample)
        .count();
    let not_proved = LIARS
        .iter()
        .filter(|(_, class)| *class == Liar::NotProved)
        .count();
    let vacuous = LIARS
        .iter()
        .filter(|(_, class)| *class == Liar::Vacuous)
        .count();
    assert_eq!(
        (counterexamples, not_proved, vacuous),
        (16, 2, 1),
        "liar verdict classes"
    );

    let witnesses: Vec<&&str> = CONTROLS
        .iter()
        .filter(|case| case.contains("witness"))
        .collect();
    assert_eq!(
        witnesses.len(),
        9,
        "satisfiability witnesses: {witnesses:?}"
    );

    // The generated lemmas are counted from the fixture, not from the list.
    let source = std::fs::read_to_string(fixture("sm_controls.rs")).expect("fixture readable");
    let raw = syn::parse_file(&source).expect("fixture parses");
    let lemmas = state_machine_dsl::machine_lemmas(&raw);
    let lemma_names: BTreeSet<String> = lemmas.iter().map(|(_, lemma, _)| lemma.clone()).collect();
    assert_eq!(
        lemma_names.len(),
        8,
        "generated INIT/IND lemmas in the controls fixture: {lemma_names:?}"
    );
    let inductive_controls: BTreeSet<String> = CONTROLS
        .iter()
        .filter(|case| case.ends_with("_inductive"))
        .map(|case| (*case).to_string())
        .collect();
    assert_eq!(
        inductive_controls, lemma_names,
        "every generated lemma is a control, and no control claims to be one without a machine"
    );

    // The lemma-bearing machines, counted the same way. (Witness coverage per
    // transition is asserted by `controls_verify` plus the witness twins in
    // `LIARS`; this only pins how many machines the count above ranges over.)
    let machines: BTreeSet<String> = lemmas
        .iter()
        .map(|(machine, _, _)| machine.clone())
        .collect();
    assert_eq!(
        machines.len(),
        4,
        "machines with generated lemmas in the controls fixture: {machines:?}"
    );
}
