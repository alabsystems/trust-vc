// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ROUND-10 REVIEW OF ROUNDS 8 AND 9: the binder and scope shapes their two
//! guards do not name, measured and found CLEAN.
//!
//! Round 8 recorded every PATTERN-bound name as an opaque binder; round 9 (a)
//! stopped the flat `let` map from speaking for a name the context DECLARES and
//! (b) made an `@` pattern record the names below its head. This file is the
//! adversarial review of both, kept as a regression rather than as prose.
//!
//! WHAT WAS PROBED AND CAME BACK FAIL-CLOSED, all at `5106f577`, cache off, over
//! an exec parameter reached through a TYPE ALIAS (the spelling round 9's guard
//! turns on) with a ghost `let` of the receiver's name somewhere else:
//!   `ra1` a doubly NESTED block · `ra2` a closure inside a closure ·
//!   `ra4` an `if let` · `ra5` a `while let` · `ra6` a `loop` that rebinds each
//!   iteration · `ra7` a `let` whose initializer is a CALL · `ra8` a qualified
//!   `<Seq<u64>>::empty()` initializer · `ra9` a `let`-`else` · `ra10` a `const`
//!   ITEM in an inner block.
//!
//! AND THE TWO DIRECTIONS OF THE MACRO, which is the one binder form NO
//! collector can see: `ra3` a ghost `let` hidden in a macro leaves the exec
//! parameter UNRESOLVED (fail closed), and `ra3b` — the dangerous direction, an
//! EXEC rebind of a genuine `Seq<u64>` parameter hidden in a macro — is rejected
//! outright by `vc_extraction`'s unsupported-macro rule rather than silently
//! keeping the parameter's ghost reading. `ra3c` is the literal-rebind control
//! and `ra3d` the liar twin: an unshadowed spec parameter still VERIFIES.
//!
//! THE `@` HALF, round 9's `pattern_bound_idents` recursion, probed at every
//! shape it recurses through and one it does not: `rb1` a NESTED `@`, `rb2` `@`
//! on a SLICE pattern, `rb3` `@` on a STRUCT pattern, `rb4` `@` on a REFERENCE
//! pattern, `rb5` `@` over an OR pattern, `rb6` `@` under a type ascription
//! (which `local_ident` declines, so round 8's opaque arm carries it), `rb7` an
//! `@` with a `ref` sub-binding. All fail closed.
//!
//! AND A RECEIVER THE CONTEXT DECLARES NOTHING FOR — round 9's guard reads
//! `get_variable_type(..).is_none()`, so a PARAMETER the seam never registered
//! would let the flat `let` map speak for it exactly as before. Fourteen
//! spellings were probed (`rd1`-`rd15`: a slice, `Option<Vec<_>>`, `HashMap`,
//! `Box<Vec<_>>`, a generic `T`, `impl Iterator`, a nested `Vec<Vec<_>>`, an
//! array, a DOUBLE alias, the fully-qualified `std::vec::Vec`, `VecDeque`, a
//! user struct, a tuple, a reference-to-alias and `BinaryHeap`), each against
//! the SAME body with the inner `let` RENAMED. Every one fails closed, and no
//! pair diverges — i.e. no spelling buys the skip with an unrelated statement.
//! `assert_control_agrees` keeps that last claim EXECUTABLE rather than prose:
//! all fifteen probe/control pairs must land on the same verdict KIND, so a
//! future spelling that buys the skip fires this file instead of going unseen.
//!
//! THE DECISIVE-PAIR BAR runs over every shape: each `_cx` is paired with the
//! `_nosink` twin that defines the identical closure and hands it to nothing.
//! Adding a use may never remove an obligation.
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn repro_path() -> String {
    format!(
        "{}/tests/data/closure_binder_round10_repro.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn verify(path: &str, func: &str) -> Result<VerifyResult, trust_vc_core::TrustVcError> {
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(path, func)
    })
}

fn assert_not_verified(path: &str, func: &str) {
    if let Ok(VerifyResult::Verified) = verify(path, func) {
        panic!("ESCAPING-CLOSURE FALSE-VERIFY: `{func}` must not verify")
    }
}

fn assert_verified(path: &str, func: &str) {
    let v = verify(path, func).unwrap_or_else(|e| panic!("verify `{func}` failed: {e:?}"));
    assert!(
        matches!(v, VerifyResult::Verified),
        "OVER-REJECTION: `{func}` must verify; got {v:?}"
    );
}

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

/// The DECISIVE-CONTROL bar for the `rd` probes: the same body with the inner
/// ghost `let` RENAMED. If a spelling ever buys the ghost skip with that
/// unrelated statement, the probe and its control DIVERGE and this fires —
/// which is the shape every finding from round 5 onward has had.
fn assert_control_agrees(path: &str, probe: &str, control: &str) {
    let kind = |r: &Result<VerifyResult, trust_vc_core::TrustVcError>| match r {
        Ok(VerifyResult::Verified) => "Verified",
        Ok(VerifyResult::Counterexample { .. }) => "Counterexample",
        Ok(VerifyResult::Unknown { .. }) => "Unknown",
        Ok(VerifyResult::Error { .. }) => "Error",
        Ok(_) => "OtherOk",
        Err(_) => "ExtractionErr",
    };
    let (a, b) = (verify(path, probe), verify(path, control));
    assert_eq!(
        kind(&a),
        kind(&b),
        "DECISIVE CONTROL DIVERGED: `{probe}` -> {} but the same body with the \
         inner `let` RENAMED, `{control}`, -> {}. An unrelated statement in a \
         scope the receiver is not in changed the verdict.",
        kind(&a),
        kind(&b)
    );
}

#[test]
fn round10_every_probed_binder_and_scope_shape_fails_closed() {
    let p = repro_path();
    for f in [
        "ra10_const_item_shadow_cx",
        "ra1_nested_block_cx",
        "ra2_nested_closure_cx",
        "ra3_macro_hidden_ghost_let_cx",
        "ra3b_macro_hidden_exec_rebind_cx",
        "ra3c_literal_exec_rebind_cx",
        "ra4_if_let_cx",
        "ra5_while_let_cx",
        "ra6_loop_rebind_cx",
        "ra7_init_is_call_cx",
        "ra8_init_is_qualified_call_cx",
        "ra9_let_else_cx",
        "rb1_nested_at_cx",
        "rb2_at_on_slice_cx",
        "rb3_at_on_struct_pattern_cx",
        "rb4_at_on_reference_pattern_cx",
        "rb5_at_or_subpattern_cx",
        "rb6_at_under_type_ascription_cx",
        "rb7_at_ref_binding_cx",
        "rd10_fully_qualified_cx",
        "rd10_fully_qualifiedb_control_cx",
        "rd11_vecdeque_cx",
        "rd11_vecdequeb_control_cx",
        "rd12_user_struct_cx",
        "rd12_user_structb_control_cx",
        "rd13_tuple_param_cx",
        "rd13_tuple_paramb_control_cx",
        "rd14_ref_alias_cx",
        "rd14_ref_aliasb_control_cx",
        "rd15_binary_heap_cx",
        "rd15_binary_heapb_control_cx",
        "rd1_slice_ref_cx",
        "rd1_slice_refb_control_cx",
        "rd2_option_vec_cx",
        "rd2_option_vecb_control_cx",
        "rd3_hashmap_cx",
        "rd3_hashmapb_control_cx",
        "rd4_box_vec_cx",
        "rd4_box_vecb_control_cx",
        "rd5_generic_param_cx",
        "rd5b_generic_param_control_cx",
        "rd6_impl_iterator_cx",
        "rd6_impl_iteratorb_control_cx",
        "rd7_nested_vec_cx",
        "rd7_nested_vecb_control_cx",
        "rd8_array_cx",
        "rd8_arrayb_control_cx",
        "rd9_double_alias_cx",
        "rd9_double_aliasb_control_cx",
    ] {
        assert_not_verified(&p, f);
    }
    {
        let f = "ra3d_plain_spec_receiver_ok";
        assert_verified(&p, f);
    }
    for (with_sink, without_sink) in [
        ("ra10_const_item_shadow_cx", "ra10_const_item_shadow_nosink"),
        ("ra1_nested_block_cx", "ra1_nested_block_nosink"),
        ("ra2_nested_closure_cx", "ra2_nested_closure_nosink"),
        (
            "ra3b_macro_hidden_exec_rebind_cx",
            "ra3b_macro_hidden_exec_rebind_nosink",
        ),
        ("ra4_if_let_cx", "ra4_if_let_nosink"),
        ("ra5_while_let_cx", "ra5_while_let_nosink"),
        ("ra6_loop_rebind_cx", "ra6_loop_rebind_nosink"),
        ("ra7_init_is_call_cx", "ra7_init_is_call_nosink"),
        (
            "ra8_init_is_qualified_call_cx",
            "ra8_init_is_qualified_call_nosink",
        ),
        ("ra9_let_else_cx", "ra9_let_else_nosink"),
        ("rb1_nested_at_cx", "rb1_nested_at_nosink"),
        ("rb2_at_on_slice_cx", "rb2_at_on_slice_nosink"),
        (
            "rb3_at_on_struct_pattern_cx",
            "rb3_at_on_struct_pattern_nosink",
        ),
        (
            "rb4_at_on_reference_pattern_cx",
            "rb4_at_on_reference_pattern_nosink",
        ),
        ("rb5_at_or_subpattern_cx", "rb5_at_or_subpattern_nosink"),
        (
            "rb6_at_under_type_ascription_cx",
            "rb6_at_under_type_ascription_nosink",
        ),
        ("rb7_at_ref_binding_cx", "rb7_at_ref_binding_nosink"),
        ("rd10_fully_qualified_cx", "rd10_fully_qualified_nosink"),
        ("rd11_vecdeque_cx", "rd11_vecdeque_nosink"),
        ("rd12_user_struct_cx", "rd12_user_struct_nosink"),
        ("rd13_tuple_param_cx", "rd13_tuple_param_nosink"),
        ("rd14_ref_alias_cx", "rd14_ref_alias_nosink"),
        ("rd15_binary_heap_cx", "rd15_binary_heap_nosink"),
        ("rd1_slice_ref_cx", "rd1_slice_ref_nosink"),
        ("rd2_option_vec_cx", "rd2_option_vec_nosink"),
        ("rd3_hashmap_cx", "rd3_hashmap_nosink"),
        ("rd4_box_vec_cx", "rd4_box_vec_nosink"),
        ("rd5_generic_param_cx", "rd5_generic_param_nosink"),
        ("rd6_impl_iterator_cx", "rd6_impl_iterator_nosink"),
        ("rd7_nested_vec_cx", "rd7_nested_vec_nosink"),
        ("rd8_array_cx", "rd8_array_nosink"),
        ("rd9_double_alias_cx", "rd9_double_alias_nosink"),
    ] {
        assert_sink_does_not_weaken(&p, with_sink, without_sink);
    }
    for (probe, control) in [
        (
            "rd10_fully_qualified_cx",
            "rd10_fully_qualifiedb_control_cx",
        ),
        ("rd11_vecdeque_cx", "rd11_vecdequeb_control_cx"),
        ("rd12_user_struct_cx", "rd12_user_structb_control_cx"),
        ("rd13_tuple_param_cx", "rd13_tuple_paramb_control_cx"),
        ("rd14_ref_alias_cx", "rd14_ref_aliasb_control_cx"),
        ("rd15_binary_heap_cx", "rd15_binary_heapb_control_cx"),
        ("rd1_slice_ref_cx", "rd1_slice_refb_control_cx"),
        ("rd2_option_vec_cx", "rd2_option_vecb_control_cx"),
        ("rd3_hashmap_cx", "rd3_hashmapb_control_cx"),
        ("rd4_box_vec_cx", "rd4_box_vecb_control_cx"),
        ("rd6_impl_iterator_cx", "rd6_impl_iteratorb_control_cx"),
        ("rd7_nested_vec_cx", "rd7_nested_vecb_control_cx"),
        ("rd8_array_cx", "rd8_arrayb_control_cx"),
        ("rd9_double_alias_cx", "rd9_double_aliasb_control_cx"),
        ("rd5_generic_param_cx", "rd5b_generic_param_control_cx"),
    ] {
        assert_control_agrees(&p, probe, control);
    }
}
