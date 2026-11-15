// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ROUND-10 SOUNDNESS: a BARE NAME is not a spec collection.
//!
//! Every ghost reading in the closure lane keys on one of six bare names —
//! `Seq`/`Set`/`Map`/`Multiset` for the spec-collection TYPE table
//! (`param_extract::syn_type_string_is_spec_collection`) and the ghost
//! CONSTRUCTOR path (`Seq::new(..)`), plus `SpecFn`/`FnSpec` for the ghost
//! closure SINK. Round 9 (`5106f577`) closed ONE shape of one of them: it made
//! the TYPE table require the element arguments, which rules out a bare
//! monomorphic alias `type Seq = Vec<u64>` and rules out nothing else. Round 9
//! disclosed the generic half as still open and named
//! `ghost_collection_constructor_path` as keying on the same four names without
//! measuring it.
//!
//! MEASURED AT `5106f577`, cache off, every one `Verified` on a body that
//! ALWAYS divides by zero, and every one against the IDENTICAL body whose only
//! difference is the NAME:
//!
//!   `rs1` `type Seq<T> = Vec<T>;` at a PARAMETER   (`rs1b` `Vec<u64>` checked)
//!   `rs2` the same through a module RE-EXPORT      (`rs2b` `BTreeSet` checked)
//!   `rs5` the same at a struct FIELD               (round 7's field seam)
//!   `rs6` the same at a `let` ANNOTATION
//!   `rt1` `type Seq = Vec<u64>;` + `Seq::new()`    (`rt1b`/`rt1c` checked)
//!   `rt2` `type Set = BTreeSet<u64>;` + `Set::new()`
//!   `rt6` the module-qualified `std::collections::Seq::new()`
//!   `ru1` a user `struct Seq` + `Seq::new()`
//!   `ru2` the CONSTRUCTOR-AS-SINK `Seq::build(n, |i| ..)` (`ru2b` checked)
//!   `ru3` `type SpecFn = u64;` + `SpecFn::new(|x| ..)`    (`ru3b` checked)
//!   `ru5` the turbofish `Seq::<u64>::new()`
//!
//! THE FIX: the names a SOURCE ITEM of the file defines are recorded on the
//! `VerificationContext` (`register_shadowed_spec_name`, filled from the source
//! registry's `structs`/`enums`/`type_aliases` and its `ambiguous_type_names`),
//! and every one of those readings falls through to `Unknown`/not-ghost for a
//! name the file redefines. `Unknown` fails closed into a definition-site body
//! check.
//!
//! WHAT IT COSTS, and why this file cannot be satisfied by refusing the ghost
//! surface: `rv1`-`rv7` are the GENUINE spec spellings in a file that redefines
//! nothing — parameter, struct field, `let` annotation, bare ghost constructor,
//! the ghost constructor as a SINK, `SpecFn::new`, and a spec tuple component —
//! and every one of them must keep VERIFYING, with `rv1b`/`rv7b` the refuted
//! halves at the same element width behind an EXEC container. The one real cost
//! is the file that DEFINES the ghost types themselves (vstd's own `seq.rs`):
//! there the skip is refused, which is the sound direction.
//!
//! `rs3` (a lifetime-argument-only `struct Map<'a>`) and `rs4` (a const-generic
//! `struct Multiset<3>`) were measured fail-closed at `5106f577` ALREADY, for an
//! unrelated reason — the context reports an unrecognized variable sort — so
//! they are ratchets here, not attribution.
//!
//! NEUTRALIZATIONS, each over this file plus
//! `closure_binder_round10_soundness`, restore by `git checkout`, `git diff`
//! empty after every one:
//!   G23 the whole scope rule off (`spec_name_is_shadowed` -> `false`): 2/4 —
//!       `rs`, `rt`, `ru` and `rw` ALL red with FALSE VERIFIES (`rs1`, `rt1`,
//!       `ru1`, `rw1`), while `rv` (the liar twins) and `ry` stay GREEN and
//!       `closure_binder_round10_soundness` stays 1/0. Over the WHOLE closure
//!       suite it is 130/0 — no collateral at all.
//!   G24 the CONSTRUCTOR-path + `SpecFn` half only: 3/3 — `rt`, `ru`, `rw`
//!       (`rw2`, the ctor route); `rs` GREEN.
//!   G25 the TYPE-TABLE half only: 4/2 — `rs`, `rw` (`rw1`, the parameter
//!       route); `rt`, `ru` GREEN. G24 and G25 are exact mirrors, so neither
//!       half is redundant and neither covers the other's routes.
//!   G26 the VIEW receiver gate off: 5/1 — EXACTLY `ry`, false verify on `ry1`.
//!   G27 the `const`/`static` binder recording off: 5/1 — EXACTLY `ry`, false
//!       verify on `ry6`.
//!
//! CACHE DISCIPLINE: every verdict is recomputed with
//! `TRUST_VC_DISABLE_VC_CACHE=1`; the on-disk cache stores only `Verified`.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn fixture(name: &str) -> String {
    format!("{}/tests/data/{}", env!("CARGO_MANIFEST_DIR"), name)
}

fn verify(path: &str, func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(path, func)
    })
}

/// An extraction `Err` and any solver non-`Verified` are sound non-verifies;
/// only `Verified` is the false-verify.
fn assert_not_verified(path: &str, func: &str) {
    if let Ok(VerifyResult::Verified) = verify(path, func) {
        panic!("SPEC-NAME-SHADOW FALSE-VERIFY: `{func}` must not verify")
    }
}

fn assert_verified(path: &str, func: &str) {
    let v = verify(path, func).unwrap_or_else(|e| panic!("verify `{func}` failed: {e:?}"));
    assert!(
        matches!(v, VerifyResult::Verified),
        "OVER-REJECTION: `{func}` must verify; got {v:?}"
    );
}

fn assert_counterexample(path: &str, func: &str) {
    let v = verify(path, func).unwrap_or_else(|e| panic!("verify `{func}` failed: {e:?}"));
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "EXPECTED A REFUTATION: `{func}`; got {v:?}"
    );
}

/// THE DECISIVE-PAIR BAR: `with_sink` and `without_sink` are the SAME closure
/// body, one handed to a collection sink and one not. Adding a use may never
/// remove an obligation.
fn assert_sink_does_not_weaken(path: &str, with_sink: &str, without_sink: &str) {
    let bare = verify(path, without_sink);
    if matches!(bare, Ok(VerifyResult::Verified)) {
        return;
    }
    let sunk = verify(path, with_sink);
    assert!(
        !matches!(sunk, Ok(VerifyResult::Verified)),
        "SINK DISABLED THE CHECK: `{without_sink}` -> {bare:?}, but the identical \
         body handed to a sink made `{with_sink}` -> Verified."
    );
}

#[test]
fn rs1_rs6_a_user_generic_named_seq_is_not_a_spec_collection() {
    let p = fixture("spec_name_scope_generic_repro.rs");
    for f in [
        "rs1_generic_alias_seq_cx",
        "rs2_reexport_generic_set_cx",
        "rs5_field_spelled_with_generic_alias_cx",
        "rs6_generic_alias_local_let_cx",
        // ratchets: fail-closed at `5106f577` already, for an unrelated reason.
        "rs3_lifetime_only_map_cx",
        "rs4_const_generic_multiset_cx",
        // the decisive controls, at the std spellings the aliases name.
        "rs1b_control_plain_vec_cx",
        "rs2b_control_plain_btreeset_cx",
    ] {
        assert_not_verified(&p, f);
    }
    for (with, without) in [
        ("rs1_generic_alias_seq_cx", "rs1_generic_alias_seq_nosink"),
        (
            "rs2_reexport_generic_set_cx",
            "rs2_reexport_generic_set_nosink",
        ),
        (
            "rs5_field_spelled_with_generic_alias_cx",
            "rs5_field_spelled_with_generic_alias_nosink",
        ),
        (
            "rs6_generic_alias_local_let_cx",
            "rs6_generic_alias_local_let_nosink",
        ),
        ("rs3_lifetime_only_map_cx", "rs3_lifetime_only_map_nosink"),
        (
            "rs4_const_generic_multiset_cx",
            "rs4_const_generic_multiset_nosink",
        ),
    ] {
        assert_sink_does_not_weaken(&p, with, without);
    }
}

#[test]
fn rt1_rt6_a_ghost_constructor_path_is_a_bare_name() {
    let p = fixture("spec_name_scope_ctor_repro.rs");
    for f in [
        "rt1_ctor_alias_named_seq_cx",
        "rt2_ctor_alias_named_set_cx",
        "rt3_ctor_annotated_alias_cx",
        "rt6_ctor_module_qualified_cx",
        // the decisive controls: the identical bodies at names that collide
        // with nothing. Non-verifies BEFORE the fix as well, which is what
        // attributes `rt1`/`rt2`/`rt6` to the NAME and not to the body.
        "rt1b_ctor_control_plain_alias_cx",
        "rt1c_ctor_control_std_vec_cx",
        "rt2b_ctor_control_btreeset_cx",
    ] {
        assert_not_verified(&p, f);
    }
    for (with, without) in [
        (
            "rt1_ctor_alias_named_seq_cx",
            "rt1_ctor_alias_named_seq_nosink",
        ),
        (
            "rt2_ctor_alias_named_set_cx",
            "rt2_ctor_alias_named_set_nosink",
        ),
        (
            "rt3_ctor_annotated_alias_cx",
            "rt3_ctor_annotated_alias_nosink",
        ),
        (
            "rt6_ctor_module_qualified_cx",
            "rt6_ctor_module_qualified_nosink",
        ),
    ] {
        assert_sink_does_not_weaken(&p, with, without);
    }
}

#[test]
fn ru1_ru5_a_user_struct_and_the_specfn_sink_carry_the_same_defect() {
    let p = fixture("spec_name_scope_struct_repro.rs");
    for f in [
        "ru1_user_struct_named_seq_ctor_cx",
        "ru2_ctor_as_sink_cx",
        "ru3_specfn_sink_cx",
        "ru5_ctor_turbofish_cx",
        // the decisive controls.
        "ru2b_ctor_as_sink_control_cx",
        "ru3b_specfn_sink_control_cx",
        "ru4_ctor_chain_cx",
    ] {
        assert_not_verified(&p, f);
    }
    for (with, without) in [
        (
            "ru1_user_struct_named_seq_ctor_cx",
            "ru1_user_struct_named_seq_ctor_nosink",
        ),
        ("ru2_ctor_as_sink_cx", "ru2_ctor_as_sink_nosink"),
        ("ru3_specfn_sink_cx", "ru3_specfn_sink_nosink"),
        ("ru5_ctor_turbofish_cx", "ru5_ctor_turbofish_nosink"),
    ] {
        assert_sink_does_not_weaken(&p, with, without);
    }
}

#[test]
fn rw1_rw4_an_item_that_is_not_a_type_declaration_shadows_just_as_completely() {
    let p = fixture("spec_name_scope_item_repro.rs");
    for f in [
        "rw1_use_alias_param_cx",
        "rw2_use_alias_ctor_cx",
        "rw3_trait_named_multiset_ctor_cx",
        "rw4_trait_named_multiset_param_cx",
        "rw5_control_plain_vec_cx",
        "rw7_exec_set_same_body_cx",
    ] {
        assert_not_verified(&p, f);
    }
    // PER NAME, not per file: `Set` is redefined by nothing in that file and an
    // honest spec body over it must still verify there.
    assert_verified(&p, "rw6_unshadowed_spec_set_ok");
    for (with, without) in [
        ("rw1_use_alias_param_cx", "rw1_use_alias_param_nosink"),
        ("rw2_use_alias_ctor_cx", "rw2_use_alias_ctor_nosink"),
        (
            "rw3_trait_named_multiset_ctor_cx",
            "rw3_trait_named_multiset_ctor_nosink",
        ),
        (
            "rw4_trait_named_multiset_param_cx",
            "rw4_trait_named_multiset_param_nosink",
        ),
    ] {
        assert_sink_does_not_weaken(&p, with, without);
    }
}

/// ROUND 10, the THIRD bare-name table in this lane and the one keyed on a
/// METHOD: `view`/`deep_view`/`to_seq`/`to_set`/`to_multiset` answered `Ghost`
/// for ANY receiver. This is round 2's `e15` finding (a ghost-sink METHOD NAME
/// is not a ghost closure) one table over. Measured at `5106f577`,
/// `h.view().map(|_x| 10 / 0)` over a user `struct Hv { d: Vec<u64> }`
/// published `Verified`, and so did `to_seq` and `deep_view`, while the
/// exec-field control `h.d.map(..)` in the same file was CHECKED.
///
/// AND the in-body `const`/`static` ITEM, which `LetBindingCollector` never
/// visited because it is a `Stmt::Item`. Recorded as a binder-visibility fix of
/// round 8's class: no WELL-TYPED false verify was constructed from it.
#[test]
fn ry1_ry7_a_view_is_a_spec_value_only_of_a_measured_collection() {
    let p = fixture("spec_view_receiver_repro.rs");
    for f in [
        "ry1_user_view_returns_exec_cx",
        "ry2_user_to_seq_returns_exec_cx",
        "ry3_user_deep_view_returns_exec_cx",
        "ry4_control_plain_field_cx",
        "ry5c_exec_vec_direct_cx",
        "ry6_const_item_shadows_spec_param_cx",
        "ry7_static_item_shadows_spec_param_cx",
    ] {
        assert_not_verified(&p, f);
    }
    // THE LIAR TWINS: a view of a receiver the seam HAS measured is still a
    // spec value, and an in-body `const` of some OTHER name changes nothing.
    for f in [
        "ry5_genuine_view_of_exec_vec_ok",
        "ry5b_genuine_view_of_spec_seq_ok",
        "ry8_const_item_other_name_ok",
    ] {
        assert_verified(&p, f);
    }
    for (with, without) in [
        (
            "ry1_user_view_returns_exec_cx",
            "ry1_user_view_returns_exec_nosink",
        ),
        (
            "ry2_user_to_seq_returns_exec_cx",
            "ry2_user_to_seq_returns_exec_nosink",
        ),
        (
            "ry3_user_deep_view_returns_exec_cx",
            "ry3_user_deep_view_returns_exec_nosink",
        ),
        (
            "ry6_const_item_shadows_spec_param_cx",
            "ry6_const_item_shadows_spec_param_nosink",
        ),
        (
            "ry7_static_item_shadows_spec_param_cx",
            "ry7_static_item_shadows_spec_param_nosink",
        ),
    ] {
        assert_sink_does_not_weaken(&p, with, without);
    }
}

#[test]
fn rv1_rv7_the_genuine_spec_surface_is_untouched() {
    let p = fixture("spec_name_scope_control_repro.rs");
    for f in [
        "rv1_genuine_spec_param_ok",
        "rv2_genuine_spec_field_ok",
        "rv3_genuine_spec_local_let_ok",
        "rv4_genuine_ctor_local_ok",
        "rv5_genuine_ctor_sink_ok",
        "rv6_genuine_specfn_sink_ok",
        "rv7_genuine_spec_tuple_component_ok",
    ] {
        assert_verified(&p, f);
    }
    // THE REFUTED HALVES, so the seven pins above cannot be satisfied by
    // "collection receivers are always skipped".
    assert_counterexample(&p, "rv1b_exec_param_cx");
    assert_counterexample(&p, "rv7b_exec_tuple_component_cx");
}
