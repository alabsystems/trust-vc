//! Collection metadata, length, kind, and domain tests for AstExpressionParser.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

// quality-audit: allow-file allow-rust-size — the collection-metadata unit tests of one parser module
use ay_dpll::api::Sort;
use std::collections::HashMap;

use super::make_solver;
#[cfg(feature = "native-seq")]
use crate::encoder::parser_state::{native_seq_shadow_var_name, NativeSeqShadow};
use crate::encoder::parser_state::{
    AstExpressionParser, CollectionKind, CollectionMeta, DerivedSeqView, DerivedSeqViewKind,
};

#[test]
fn test_collection_meta_prepopulated_for_seq() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let pw = crate::ir::pointer_width();
    let s = solver.declare_const("s", Sort::array(Sort::bitvec(pw), Sort::bitvec(32)));
    variables.insert("s".to_string(), s);
    var_types.insert(
        "s".to_string(),
        crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    );

    let s_len = solver.bv_var("s_len", pw);
    collection_lengths.insert("s".to_string(), s_len);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let meta = parser
        .collection_meta_by_term
        .get(&s)
        .expect("Seq variable should have collection metadata");
    assert_eq!(meta.kind, CollectionKind::Seq);
    assert_eq!(meta.len_term, Some(s_len));
    assert_eq!(
        meta.elem_ty.as_ref(),
        Some(&crate::ir::TrustVcType::Int { width: 32 }),
        "Seq metadata should have elem_ty populated"
    );
}

#[test]
fn test_collection_meta_prepopulated_for_multiset() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let ms = solver.declare_const("ms", Sort::array(Sort::bitvec(32), Sort::Int));
    variables.insert("ms".to_string(), ms);
    var_types.insert(
        "ms".to_string(),
        crate::ir::TrustVcType::Multiset(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    );

    let pw = crate::ir::pointer_width();
    let ms_len = solver.bv_var("ms_len", pw);
    collection_lengths.insert("ms".to_string(), ms_len);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let meta = parser
        .collection_meta_by_term
        .get(&ms)
        .expect("Multiset variable should have collection metadata");
    assert_eq!(meta.kind, CollectionKind::Multiset);
    assert_eq!(meta.len_term, Some(ms_len));
    assert_eq!(
        meta.elem_ty.as_ref(),
        Some(&crate::ir::TrustVcType::Int { width: 32 }),
        "Multiset metadata should have elem_ty populated"
    );
}

#[test]
fn test_lookup_collection_len_term_first_then_name_fallback() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let pw = crate::ir::pointer_width();
    let s = solver.declare_const("s", Sort::array(Sort::bitvec(pw), Sort::bitvec(32)));
    let s_len = solver.bv_var("s_len", pw);
    let fake_term = solver.bv_var("fake", pw);

    variables.insert("s".to_string(), s);
    var_types.insert(
        "s".to_string(),
        crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    );
    collection_lengths.insert("s".to_string(), s_len);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert_eq!(
        parser.lookup_collection_len(s, Some("s")),
        Some(s_len),
        "lookup_collection_len should resolve via term metadata"
    );
    assert_eq!(
        parser.lookup_collection_len(fake_term, Some("s")),
        Some(s_len),
        "lookup_collection_len should fall back to name-keyed map"
    );
    assert_eq!(
        parser.lookup_collection_len(fake_term, Some("nonexistent")),
        None,
        "unknown term + unknown name should return None"
    );
}

#[test]
fn test_lookup_collection_kind_resolves_from_metadata_and_var_types() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let pw = crate::ir::pointer_width();
    let s = solver.declare_const("s", Sort::array(Sort::bitvec(pw), Sort::bitvec(32)));
    let s_len = solver.bv_var("s_len", pw);
    let fake_term = solver.bv_var("fake2", pw);

    variables.insert("s".to_string(), s);
    var_types.insert(
        "s".to_string(),
        crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    );
    collection_lengths.insert("s".to_string(), s_len);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert_eq!(
        parser.lookup_collection_kind(s, Some("s")),
        Some(CollectionKind::Seq)
    );
    assert_eq!(
        parser.lookup_collection_kind(fake_term, Some("s")),
        Some(CollectionKind::Seq),
        "should fall back to var_types for unknown term"
    );
}

#[test]
fn test_lookup_collection_kind_falls_back_to_multiset_var_type() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let ms = solver.declare_const("ms", Sort::array(Sort::bitvec(32), Sort::Int));
    let fake_term = solver.declare_const("fake_ms_term", Sort::array(Sort::bitvec(32), Sort::Int));

    variables.insert("ms".to_string(), ms);
    var_types.insert(
        "ms".to_string(),
        crate::ir::TrustVcType::Multiset(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    );

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert_eq!(
        parser.lookup_collection_kind(fake_term, Some("ms")),
        Some(CollectionKind::Multiset),
        "should fall back to var_types for Multiset receivers without term metadata"
    );
}

// --- Map domain terms ---

#[test]
fn test_map_domain_terms_prepopulated() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let m = solver.declare_const("m", Sort::array(Sort::bitvec(32), Sort::bitvec(32)));
    variables.insert("m".to_string(), m);
    var_types.insert(
        "m".to_string(),
        crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
        ),
    );
    let m_dom = solver.declare_const("m_dom", Sort::array(Sort::bitvec(32), Sort::Bool));
    variables.insert("m_dom".to_string(), m_dom);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    assert!(
        parser.domain_terms.contains_key("m_dom"),
        "Map domain term should be pre-populated from variables"
    );
    assert_eq!(
        parser.domain_terms.get("m_dom"),
        Some(&m_dom),
        "domain term should match the declared m_dom variable"
    );
}

// --- register_collection_meta ---

#[test]
fn test_register_collection_meta_updates_term_widths() {
    let mut solver = make_solver();
    let pw = crate::ir::pointer_width();
    let new_term = solver.declare_const("result", Sort::array(Sort::bitvec(pw), Sort::bitvec(32)));
    let new_len = solver.bv_var("result_len", pw);

    let variables = HashMap::new();
    let var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.register_collection_meta(
        new_term,
        CollectionMeta {
            kind: CollectionKind::Seq,
            len_term: Some(new_len),
            len_guard: None,
            elem_ty: Some(crate::ir::TrustVcType::Int { width: 32 }),
            key_ty: None,
            dom_term: None,
        },
    );

    assert!(
        parser.collection_meta_by_term.contains_key(&new_term),
        "registered term should be in metadata map"
    );
    assert_eq!(
        parser.term_widths.get(&new_len),
        Some(&(pw, false)),
        "length term should be registered as pointer-width unsigned"
    );
}

#[test]
fn test_register_and_lookup_derived_seq_view() {
    let mut solver = make_solver();
    let pw = crate::ir::pointer_width();
    let source = solver.declare_const(
        "source_seq",
        Sort::array(Sort::bitvec(pw), Sort::bitvec(32)),
    );
    let view = solver.declare_const("derived_set", Sort::array(Sort::bitvec(32), Sort::Bool));

    let variables = HashMap::new();
    let var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.register_derived_seq_view(
        view,
        DerivedSeqView {
            kind: DerivedSeqViewKind::SetView,
            source_term: source,
            source_name: Some("s".to_string()),
        },
    );

    let stored = parser
        .lookup_derived_seq_view(view)
        .expect("derived view metadata should be retrievable by term");
    assert_eq!(stored.kind, DerivedSeqViewKind::SetView);
    assert_eq!(stored.source_term, source);
    assert_eq!(stored.source_name.as_deref(), Some("s"));
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_shadow_prepopulated_for_declared_seq() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let seq_sort = Sort::seq(Sort::bitvec(32));
    let s = solver.declare_const("s", seq_sort.clone());
    let shadow_name = native_seq_shadow_var_name("s");
    let shadow = solver.declare_const(&shadow_name, seq_sort);
    let s_len = solver.int_var("s_len");

    variables.insert("s".to_string(), s);
    variables.insert(shadow_name, shadow);
    var_types.insert(
        "s".to_string(),
        crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    );
    collection_lengths.insert("s".to_string(), s_len);

    let parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let shadow_meta = parser
        .lookup_native_seq_shadow(s)
        .expect("declared Seq should expose a pre-populated native shadow");
    assert_eq!(shadow_meta.native_term, shadow);
    assert_eq!(shadow_meta.source_term, s);
    assert_eq!(shadow_meta.source_name.as_deref(), Some("s"));
    assert_eq!(
        shadow_meta.elem_ty,
        crate::ir::TrustVcType::Int { width: 32 }
    );
    assert_eq!(
        parser.solver.term_sort(shadow_meta.len_int_term),
        Sort::Int,
        "native shadow length should stay Int-sorted"
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_register_and_lookup_native_seq_shadow() {
    let mut solver = make_solver();
    let source = solver.declare_const("source_seq", Sort::seq(Sort::bitvec(32)));
    let shadow = solver.declare_const("shadow_seq", Sort::seq(Sort::bitvec(32)));
    let shadow_len = solver.int_var("shadow_len");

    let variables = HashMap::new();
    let var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.register_native_seq_shadow(
        source,
        NativeSeqShadow {
            native_term: shadow,
            len_int_term: shadow_len,
            source_term: source,
            source_name: Some("s".to_string()),
            elem_ty: crate::ir::TrustVcType::Int { width: 32 },
        },
    );

    let stored = parser
        .lookup_native_seq_shadow(source)
        .expect("registered native shadow metadata should be retrievable");
    assert_eq!(stored.native_term, shadow);
    assert_eq!(stored.len_int_term, shadow_len);
    assert_eq!(stored.source_term, source);
    assert_eq!(stored.source_name.as_deref(), Some("s"));
    assert_eq!(stored.elem_ty, crate::ir::TrustVcType::Int { width: 32 });
}

#[test]
fn test_emit_collection_len_guard_queues_only_registered_guard() {
    let mut solver = make_solver();
    let pw = crate::ir::pointer_width();
    let guarded_term =
        solver.declare_const("guarded", Sort::array(Sort::bitvec(pw), Sort::bitvec(32)));
    let unguarded_term =
        solver.declare_const("unguarded", Sort::array(Sort::bitvec(pw), Sort::bitvec(32)));
    let unknown_term =
        solver.declare_const("unknown", Sort::array(Sort::bitvec(pw), Sort::bitvec(32)));
    let guarded_len = solver.bv_var("guarded_len", pw);
    let unguarded_len = solver.bv_var("unguarded_len", pw);
    let len_guard = solver.declare_const("len_guard", Sort::Bool);

    let variables = HashMap::new();
    let var_types = HashMap::new();
    let functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    parser.register_collection_meta(
        guarded_term,
        CollectionMeta {
            kind: CollectionKind::Seq,
            len_term: Some(guarded_len),
            len_guard: Some(("guarded len access".to_string().into(), len_guard)),
            elem_ty: Some(crate::ir::TrustVcType::Int { width: 32 }),
            key_ty: None,
            dom_term: None,
        },
    );
    parser.register_collection_meta(
        unguarded_term,
        CollectionMeta {
            kind: CollectionKind::Seq,
            len_term: Some(unguarded_len),
            len_guard: None,
            elem_ty: Some(crate::ir::TrustVcType::Int { width: 32 }),
            key_ty: None,
            dom_term: None,
        },
    );

    parser.emit_collection_len_guard(unguarded_term);
    parser.emit_collection_len_guard(unknown_term);
    assert!(
        parser.overflow_checks.is_empty(),
        "unguarded and unknown terms should not queue length guards"
    );

    parser.emit_collection_len_guard(guarded_term);
    assert_eq!(
        parser.overflow_checks.len(),
        1,
        "guarded length access should queue exactly one proof obligation"
    );
    assert_eq!(
        parser.overflow_checks[0].0, "guarded len access",
        "emit_collection_len_guard should preserve the stored guard label"
    );
}

// =====================================================================
// A collection reached through a UF APPLICATION (a struct FIELD in a spec
// expression lowers to `FnCall { name: <selector UF>, .. }`, never to a
// `ReadPlace`) gets dom/len companions — and the SAME place gets the SAME ones.
// =====================================================================

/// Builds `<selector>(s)` for a `Map<u32, u32>`-typed field of a receiver `s`.
fn field_selector_map_call() -> crate::ir::TrustVcExpr {
    crate::ir::TrustVcExpr::FnCall {
        name: "S__m".to_string(),
        args: vec![crate::ir::TrustVcExpr::Var {
            name: "s".to_string(),
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        return_ty: crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
        ),
    }
}

#[test]
fn collection_typed_fn_call_result_gets_dom_metadata() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let mut functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let s = solver.bv_var("s", 32);
    variables.insert("s".to_string(), s);
    var_types.insert("s".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    let decl = solver
        .try_declare_fun(
            "S__m",
            &[Sort::bitvec(32)],
            Sort::array(Sort::bitvec(32), Sort::bitvec(32)),
        )
        .expect("declare selector UF");
    functions.insert("S__m".to_string(), decl);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = field_selector_map_call();
    let term = parser
        .encode_trust_vc_expr(&expr)
        .expect("encode selector UF application");

    // THE LOAD-BEARING ASSERTION: without the `ensure_projected_collection_meta`
    // call at the end of `encode_fn_call`, this term carries no metadata and
    // `encode_contains_key` answers "not supported without dom tracking".
    let dom = parser.lookup_collection_dom(term, None);
    assert!(
        dom.is_some(),
        "a Map-typed UF application must carry a domain term so contains_key() can read it"
    );
    assert_eq!(
        parser.lookup_collection_kind(term, None),
        Some(CollectionKind::Map),
        "a Map-typed UF application must be classified as a Map"
    );
}

#[test]
fn same_field_place_encodes_to_same_term_and_same_dom() {
    let mut solver = make_solver();
    let mut variables = HashMap::new();
    let mut var_types = HashMap::new();
    let mut functions = HashMap::new();
    let mut collection_lengths = HashMap::new();

    let s = solver.bv_var("s", 32);
    variables.insert("s".to_string(), s);
    var_types.insert("s".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    let decl = solver
        .try_declare_fun(
            "S__m",
            &[Sort::bitvec(32)],
            Sort::array(Sort::bitvec(32), Sort::bitvec(32)),
        )
        .expect("declare selector UF");
    functions.insert("S__m".to_string(), decl);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let expr = field_selector_map_call();
    let first = parser
        .encode_trust_vc_expr(&expr)
        .expect("encode first occurrence");
    let first_dom = parser
        .lookup_collection_dom(first, None)
        .expect("first occurrence has a dom");
    let second = parser
        .encode_trust_vc_expr(&expr)
        .expect("encode second occurrence");
    let second_dom = parser
        .lookup_collection_dom(second, None)
        .expect("second occurrence has a dom");

    // SAME PLACE => SAME TERM. Measured, not assumed: if `try_apply` did not
    // hash-cons, each occurrence would mint an independent dom and
    // `m.contains_key(k) ==> m.contains_key(k)` would stop being provable.
    assert_eq!(
        first, second,
        "two occurrences of the same field place must encode to the same Term"
    );
    // SAME TERM => SAME DOM.
    assert_eq!(
        first_dom, second_dom,
        "two occurrences of the same field place must share one domain array"
    );

    // A DIFFERENT place must NOT share that dom.
    let other = crate::ir::TrustVcExpr::FnCall {
        name: "S__m".to_string(),
        args: vec![crate::ir::TrustVcExpr::IntLit {
            value: 7,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        return_ty: crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
        ),
    };
    let other_term = parser
        .encode_trust_vc_expr(&other)
        .expect("encode a different receiver");
    assert_ne!(
        first, other_term,
        "a different receiver must not collapse onto the same carrier term"
    );
    assert_ne!(
        Some(first_dom),
        parser.lookup_collection_dom(other_term, None),
        "a different place must not borrow another place's domain array"
    );
}
