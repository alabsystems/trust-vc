//! Match expression and pattern lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #1550 Phase 3 (#1864).

use super::operators::coerce_unsuffixed_literal;
use super::{
    infer_expr_type, lower_syn_expr_with_depth, next_lowering_depth, LoweringError, TypeEnv,
};
use crate::encoder::datatype::{tester_symbol_name, variant_symbol_name};
use crate::ir::{DatatypeVariant, TrustVcType};
use crate::ir_expr::{MatchArm, MatchPattern, StructPatternField, TrustVcExpr, TUPLE_VARIANT_NAME};
use crate::match_pattern_scope::{is_ignored_match_binding, IGNORED_MATCH_BINDING_PREFIX};
use std::collections::BTreeSet;
use syn::visit::Visit;

const MAX_EXPANDED_RANGE_PATTERN_CASES: i128 = 64;

pub(super) fn lower_match(
    m: &syn::ExprMatch,
    env: &TypeEnv,
    depth: usize,
) -> Result<TrustVcExpr, LoweringError> {
    let scrutinee = Box::new(lower_syn_expr_with_depth(&m.expr, env, depth)?);
    if m.arms.is_empty() {
        return Err(LoweringError::TypeInference(
            "cannot infer type for match expression with zero arms".into(),
        ));
    }
    let scrutinee_ty = infer_expr_type(&scrutinee);
    let mut arms = Vec::new();
    for arm in &m.arms {
        // Desugar top-level constructor VALUE sub-patterns (`Some(5)`,
        // `Point { x: 5, y }`) into a fresh binder plus an equality refinement that
        // is ANDed into the arm's guard. This reuses the encoder's verified-sound
        // guard fall-through (an arm is taken iff `pattern matches AND guard holds`,
        // else control falls to later arms) — see `encode_match`'s TRAP #2.
        let mut occupied_names = identifiers_in_arm(arm);
        let (rewritten_pat, value_refinements) =
            rewrite_value_subpatterns(&arm.pat, env, &mut occupied_names);
        let pattern = lower_pattern(&rewritten_pat, &scrutinee_ty, depth)?;
        // Extend env with bindings introduced by the pattern (incl. the fresh
        // value-subpattern binders, so the refinement below can reference them).
        let arm_env = extend_env_with_pattern(env, &pattern, &scrutinee_ty)?;
        let body = lower_syn_expr_with_depth(&arm.body, &arm_env, depth)?;
        // A match guard is lowered UNDER the arm's pattern-binding scope (it
        // references the arm's bindings) and must be a pure boolean spec expression.
        // The user guard and the value-subpattern refinements are conjoined.
        let combined_guard =
            combine_arm_guard(arm.guard.as_ref().map(|(_, g)| &**g), &value_refinements);
        let guard = match combined_guard {
            None => None,
            Some(g_expr) => {
                // Faithfulness: Verus rejects an arm that combines an or-pattern with
                // a guard (the guard's scoping over `|` alternatives is ambiguous).
                // Value refinements only arise on tuple-struct/struct patterns, never
                // on or-patterns, so this can only reject a genuine user guard.
                if matches!(pattern, MatchPattern::Or(_)) {
                    return Err(LoweringError::UnsupportedPattern(
                        "match arm containing both an or-pattern (|) and a match-guard \
                         is not supported"
                            .into(),
                    ));
                }
                let g = lower_syn_expr_with_depth(&g_expr, &arm_env, depth)?;
                // Fail closed: a non-boolean guard would sort-mismatch or misencode.
                if infer_expr_type(&g) != TrustVcType::Bool {
                    return Err(LoweringError::UnsupportedPattern(
                        "match guard must be a boolean expression".into(),
                    ));
                }
                Some(g)
            }
        };
        arms.push(MatchArm {
            pattern,
            body,
            guard,
        });
    }
    // Cross-coerce unsuffixed integer literals across arms so a definite arm type
    // (e.g. `nat` in `Succ(p) => (1 + depth(*p)) as nat`) pins a bare-literal arm
    // (`Zero => 0`) to the same sort instead of leaving it at default `Int{32}`.
    // This mirrors `lower_if`'s branch coercion; it only ever rewrites bare
    // unsuffixed literals, so well-typed matches are unaffected.
    let target_ty = arms
        .iter()
        .map(|arm| infer_expr_type(&arm.body))
        .find(|ty| !matches!(ty, TrustVcType::Int { width: 32 }))
        .or_else(|| arms.first().map(|arm| infer_expr_type(&arm.body)))
        .ok_or_else(|| {
            LoweringError::TypeInference(
                "cannot infer type for match expression with zero lowered arms".into(),
            )
        })?;
    let arms: Vec<MatchArm> = arms
        .into_iter()
        .map(|arm| MatchArm {
            pattern: arm.pattern,
            body: coerce_unsuffixed_literal(arm.body, &target_ty),
            // The guard is a boolean, never the match's value type — carry it verbatim.
            guard: arm.guard,
        })
        .collect();
    if let Some(test) = normalize_variant_test_match(&scrutinee, &scrutinee_ty, &arms) {
        return Ok(test);
    }
    Ok(TrustVcExpr::Match {
        scrutinee,
        arms,
        ty: target_ty,
    })
}

/// Collapses the exact match-bool emitted for Verus `receiver is Variant` into
/// the datatype's native tester. The parser deliberately cannot choose Result's
/// `is_ok`/`is_err` methods from the variant spelling alone: a user datatype may
/// also define `Ok` or `Err`. At this point the receiver has an authoritative
/// lowered datatype, so the tester is selected from that datatype's identity.
///
/// A direct variant constructor is reduced to its ground truth value, matching
/// the long-standing Option/Result method normalization. No other match shape is
/// folded; guards, bindings, non-boolean bodies, and non-wildcard fallbacks retain
/// ordinary match semantics.
fn normalize_variant_test_match(
    scrutinee: &TrustVcExpr,
    scrutinee_ty: &TrustVcType,
    arms: &[MatchArm],
) -> Option<TrustVcExpr> {
    let TrustVcType::Datatype {
        name: datatype_name,
        variants,
    } = scrutinee_ty
    else {
        return None;
    };
    let [positive, fallback] = arms else {
        return None;
    };
    let MatchPattern::Struct {
        variant_name,
        fields,
        has_rest: true,
    } = &positive.pattern
    else {
        return None;
    };
    if !fields.is_empty()
        || positive.guard.is_some()
        || positive.body != TrustVcExpr::BoolLit(true)
        || fallback.pattern != MatchPattern::Wildcard
        || fallback.guard.is_some()
        || fallback.body != TrustVcExpr::BoolLit(false)
        || !variants.iter().any(|variant| variant.name == *variant_name)
    {
        return None;
    }

    if let TrustVcExpr::FnCall {
        name, return_ty, ..
    } = scrutinee
    {
        if return_ty == scrutinee_ty {
            if let Some(constructed_variant) = variants
                .iter()
                .find(|variant| name == &variant_symbol_name(datatype_name, &variant.name))
            {
                return Some(TrustVcExpr::BoolLit(
                    constructed_variant.name == *variant_name,
                ));
            }
        }
    }

    Some(TrustVcExpr::FnCall {
        name: tester_symbol_name(datatype_name, variant_name),
        args: vec![scrutinee.clone()],
        return_ty: TrustVcType::Bool,
    })
}

/// Desugars top-level constructor VALUE sub-patterns into a fresh binder plus an
/// equality refinement, so the existing (verified-sound) match-guard machinery
/// checks the literal. `Some(5)` becomes `Some(__valpat) if __valpat == 5`, and
/// `Point { x: 5, y }` becomes `Point { x: __valpat, y } if __valpat == 5`.
///
/// Only a DIRECT literal (`syn::Pat::Lit`) field sub-pattern at the TOP level of a
/// tuple-struct or struct pattern is rewritten. Nested constructor sub-patterns
/// (`Some(Some(5))`), or-patterns, ranges, and everything else are returned
/// unchanged — they flow through `lower_pattern` and fail closed there if
/// unsupported. Returns the (possibly-rewritten) pattern and the refinement
/// expressions to AND into the arm's guard (empty when nothing was rewritten).
///
/// Soundness: the rewrite is behavior-preserving. `encode_match` takes a guarded
/// arm iff `pattern matches AND guard holds`, otherwise falls through to later
/// arms, and a guarded arm never seeds the unconditional default (TRAP #2) — the
/// exact semantics of a literal field pattern. The fresh binder equals the field
/// selector, so `__valpat == 5` is precisely the field's literal test.
fn rewrite_value_subpatterns(
    pat: &syn::Pat,
    env: &TypeEnv,
    occupied_names: &mut BTreeSet<String>,
) -> (syn::Pat, Vec<syn::Expr>) {
    let mut refinements: Vec<syn::Expr> = Vec::new();
    let mut next_binder_index = 0;
    match pat {
        syn::Pat::TupleStruct(tuple) => {
            let mut rewritten = tuple.clone();
            for elem in &mut rewritten.elems {
                if let syn::Pat::Lit(lit) = elem {
                    let binder =
                        value_subpattern_binder(&mut next_binder_index, env, occupied_names);
                    refinements.push(syn::parse_quote!(#binder == #lit));
                    *elem = value_binder_pattern(binder);
                }
            }
            (syn::Pat::TupleStruct(rewritten), refinements)
        }
        syn::Pat::Struct(struct_pat) => {
            let mut rewritten = struct_pat.clone();
            for field in &mut rewritten.fields {
                if let syn::Pat::Lit(lit) = field.pat.as_ref() {
                    let binder =
                        value_subpattern_binder(&mut next_binder_index, env, occupied_names);
                    refinements.push(syn::parse_quote!(#binder == #lit));
                    field.pat = Box::new(value_binder_pattern(binder));
                }
            }
            (syn::Pat::Struct(rewritten), refinements)
        }
        other => (other.clone(), refinements),
    }
}

#[derive(Default)]
struct ArmIdentifierCollector {
    names: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for ArmIdentifierCollector {
    fn visit_ident(&mut self, ident: &'ast proc_macro2::Ident) {
        self.names.insert(ident.to_string());
    }
}

/// Collects every source identifier in the arm, not only pattern bindings.
/// A synthesized pattern binding scopes over both the guard and body, so it
/// must also avoid shadowing an outer variable/constant referenced there.
fn identifiers_in_arm(arm: &syn::Arm) -> BTreeSet<String> {
    let mut collector = ArmIdentifierCollector::default();
    collector.visit_arm(arm);
    collector.names
}

/// A fresh, non-ignored, snake-case binder ident for a rewritten value sub-pattern.
/// It is referenced by the synthesized guard, so it must NOT carry the
/// ignored-binding prefix (which would make it unreferenceable) and must start
/// lowercase so `lower_pattern` treats it as a binding, not a const pattern.
fn value_subpattern_binder(
    next_index: &mut usize,
    env: &TypeEnv,
    occupied_names: &mut BTreeSet<String>,
) -> proc_macro2::Ident {
    loop {
        let candidate = format!("__trust_vc_valpat_{}", *next_index);
        *next_index += 1;
        if env.lookup(&candidate).is_none() && occupied_names.insert(candidate.clone()) {
            return proc_macro2::Ident::new(&candidate, proc_macro2::Span::call_site());
        }
    }
}

/// Wraps a binder ident in a plain irrefutable `Pat::Ident`. Built directly (syn
/// 2.0's `Pat` has no blanket `Parse`, so `parse_quote!` cannot target it).
fn value_binder_pattern(ident: proc_macro2::Ident) -> syn::Pat {
    syn::Pat::Ident(syn::PatIdent {
        attrs: Vec::new(),
        by_ref: None,
        mutability: None,
        ident,
        subpat: None,
    })
}

/// Conjoins the arm's user guard (if any) with each value-subpattern refinement,
/// yielding the combined guard expression (or `None` when there is neither). Each
/// operand is parenthesized so operator precedence cannot reassociate across the
/// synthesized `&&`.
fn combine_arm_guard(
    user_guard: Option<&syn::Expr>,
    refinements: &[syn::Expr],
) -> Option<syn::Expr> {
    let mut acc: Option<syn::Expr> = user_guard.cloned();
    for refinement in refinements {
        acc = Some(match acc {
            None => refinement.clone(),
            Some(prev) => syn::parse_quote!((#prev) && (#refinement)),
        });
    }
    acc
}

fn extend_env_with_pattern(
    env: &TypeEnv,
    pattern: &MatchPattern,
    scrutinee_ty: &TrustVcType,
) -> Result<TypeEnv, LoweringError> {
    let mut current = pattern;
    loop {
        match current {
            MatchPattern::Ident(name) => {
                return Ok(env.extend(&[(name.clone(), scrutinee_ty.clone())]));
            }
            MatchPattern::Constructor {
                variant_name,
                bindings,
                has_rest,
            } => {
                let (_, variant) = datatype_variant(scrutinee_ty, variant_name)?;
                // With a trailing `..` rest, only the LEADING bindings are named;
                // the remaining fields are ignored (mirror `Struct::has_rest`), so
                // the exact-arity equality relaxes to `bindings <= fields`.
                let arity_ok = if *has_rest {
                    bindings.len() <= variant.fields.len()
                } else {
                    variant.fields.len() == bindings.len()
                };
                if !arity_ok {
                    return Err(LoweringError::UnsupportedPattern(format!(
                        "constructor pattern '{}' expects {} binding(s), got {}",
                        variant_name,
                        variant.fields.len(),
                        bindings.len()
                    )));
                }
                let typed_bindings: Vec<_> = bindings
                    .iter()
                    .zip(variant.fields.iter())
                    .filter(|(binding, _)| !is_ignored_match_binding(binding))
                    .map(|(binding, (_, field_ty))| (binding.clone(), field_ty.clone()))
                    .collect();
                return Ok(extend_with_recursive_ref_bindings(env, &typed_bindings));
            }
            MatchPattern::Struct {
                variant_name,
                fields,
                ..
            } => {
                let (_, variant) = datatype_variant(scrutinee_ty, variant_name)?;
                let mut typed_bindings = Vec::new();
                for field in fields {
                    let Some(binding_name) = &field.binding else {
                        continue;
                    };
                    let (_, field_ty) =
                        datatype_field(variant_name, variant, field.field_name.as_str())?;
                    typed_bindings.push((binding_name.clone(), field_ty.clone()));
                }
                return Ok(extend_with_recursive_ref_bindings(env, &typed_bindings));
            }
            MatchPattern::Or(cases) => {
                if let Some(first) = cases.first() {
                    current = first;
                } else {
                    return Ok(env.clone());
                }
            }
            MatchPattern::Lit(_) | MatchPattern::Wildcard => return Ok(env.clone()),
        }
    }
}

/// Extends `env` with constructor/struct field bindings, additionally marking
/// every binding whose field type is a `RecursiveRef` (a `Box<Self>` recursive
/// child whose owning `Box`/`Rc`/`Arc` wrapper the IR erases) as an
/// erased-shared-reference variable. This makes the transparent deref `*child`
/// in a recursive spec-fn body (e.g. `Succ(p) => depth(*p)`) lower to the bound
/// carrier `child` itself — the same no-op the constructor lowering already
/// applies to `Succ(Box::new(p))`. It does NOT change the deref rule in
/// `operators.rs`; it only classifies these bindings into the existing
/// erased-reference category, which is sound because dereferencing an erased
/// ownership wrapper is the identity in the carrier-sort IR.
fn extend_with_recursive_ref_bindings(
    env: &TypeEnv,
    typed_bindings: &[(String, TrustVcType)],
) -> TypeEnv {
    let mut extended = env.extend(typed_bindings);
    for (binding, field_ty) in typed_bindings {
        if matches!(field_ty, TrustVcType::RecursiveRef(_)) {
            extended.insert_erased_shared_ref_var(binding.clone());
        }
    }
    extended
}

fn lower_pattern(
    pat: &syn::Pat,
    scrutinee_ty: &TrustVcType,
    depth: usize,
) -> Result<MatchPattern, LoweringError> {
    let current_depth = next_lowering_depth(depth)?;
    match pat {
        syn::Pat::Lit(lit) => {
            let expr = lower_syn_lit(&lit.lit)?;
            Ok(MatchPattern::Lit(expr))
        }
        syn::Pat::Ident(i) => {
            let ident = i.ident.to_string();
            // A top-level `x @ SUBPAT` is REFUTABLE: `SUBPAT` refines which
            // scrutinees the arm matches. Lowering it to the bare (irrefutable)
            // `MatchPattern::Ident(ident)` would SILENTLY DROP the refinement,
            // making the arm always-match — the cardinal false-verify (e.g.
            // `match x { n @ 0 => 5, _ => x }` would prove `result == 5`). Fail
            // closed until `@`-binding is modeled. (The nested tuple-struct /
            // struct `@` paths already reject subpatterns below.)
            if i.subpat.is_some() {
                return Err(LoweringError::UnsupportedPattern(
                    "top-level `@`-binding pattern (`x @ subpat`) is not modeled: \
                     the refinement subpattern would be silently dropped"
                        .into(),
                ));
            }
            if i.by_ref.is_none()
                && i.mutability.is_none()
                && i.subpat.is_none()
                && matches_zero_field_variant(scrutinee_ty, &ident)
            {
                Ok(MatchPattern::Constructor {
                    variant_name: ident,
                    bindings: vec![],
                    has_rest: false,
                })
            } else if ident.chars().next().is_some_and(|c| c.is_uppercase()) {
                // An UPPERCASE-initial ident that is NOT a matched zero-field
                // variant is, by Rust convention, a `const` / associated-const
                // PATTERN (refutable — it matches only scrutinees equal to the
                // const's value), not a binding. Lowering it to the irrefutable
                // `MatchPattern::Ident` drops that value refinement — a
                // false-verify (`const K = 3; match x { K => a, _ => b }` treats
                // arm 1 as always-matching). Fail closed until const-value
                // patterns are modeled. A genuine binding is snake_case (Rust
                // warns on an uppercase binding and resolves an uppercase ident
                // to an in-scope const when one exists), so this cannot silently
                // reject an idiomatic binding.
                Err(LoweringError::UnsupportedPattern(format!(
                    "const/associated-const pattern `{ident}` is not modeled: \
                     its value refinement would be silently dropped"
                )))
            } else {
                Ok(MatchPattern::Ident(ident))
            }
        }
        syn::Pat::Path(path) => {
            let Some(segment) = path.path.segments.last() else {
                return Err(LoweringError::UnsupportedPattern(
                    "path pattern without segments".into(),
                ));
            };
            Ok(MatchPattern::Constructor {
                variant_name: segment.ident.to_string(),
                bindings: vec![],
                has_rest: false,
            })
        }
        syn::Pat::TupleStruct(tuple) => {
            let Some(segment) = tuple.path.segments.last() else {
                return Err(LoweringError::UnsupportedPattern(
                    "tuple struct pattern without segments".into(),
                ));
            };
            let variant_name = segment.ident.to_string();
            let mut bindings = Vec::with_capacity(tuple.elems.len());
            let mut has_rest = false;
            for (index, elem) in tuple.elems.iter().enumerate() {
                match elem {
                    // A trailing `..` rest binds the LEADING fields and ignores the
                    // remainder (mirror `Struct::has_rest`). Only a TRAILING rest is
                    // admitted this increment: a binding appearing AFTER `..` (a
                    // middle/back rest) needs a field-index remap and is out of
                    // scope, so it falls to the fail-closed error below.
                    syn::Pat::Rest(_) => {
                        has_rest = true;
                    }
                    // A plain identifier binds the field. An identifier carrying an
                    // `@`-subpattern (`x @ 5`) is REFUTABLE; dropping the subpattern
                    // would silently mis-lower it to the irrefutable `x`, so route it
                    // to the fail-closed `other` branch until `@` is modeled.
                    syn::Pat::Ident(binding) if binding.subpat.is_none() => {
                        if has_rest {
                            return Err(LoweringError::UnsupportedPattern(
                                "unsupported pattern: a binding after `..` (middle/back rest) \
                                 in a tuple-struct pattern is not admitted; only a trailing \
                                 rest is supported"
                                    .into(),
                            ));
                        }
                        bindings.push(binding.ident.to_string())
                    }
                    syn::Pat::Wild(_) => {
                        if has_rest {
                            return Err(LoweringError::UnsupportedPattern(
                                "unsupported pattern: a binding after `..` (middle/back rest) \
                                 in a tuple-struct pattern is not admitted; only a trailing \
                                 rest is supported"
                                    .into(),
                            ));
                        }
                        bindings.push(format!(
                            "{IGNORED_MATCH_BINDING_PREFIX}{variant_name}_{index}"
                        ))
                    }
                    other => {
                        return Err(LoweringError::UnsupportedPattern(format!(
                        "unsupported constructor sub-pattern '{}'; use simple identifier bindings or '_'",
                        quote::quote!(#other)
                    )))
                    }
                }
            }
            Ok(MatchPattern::Constructor {
                variant_name,
                bindings,
                has_rest,
            })
        }
        syn::Pat::Struct(struct_pat) => {
            let Some(segment) = struct_pat.path.segments.last() else {
                return Err(LoweringError::UnsupportedPattern(
                    "struct pattern without segments".into(),
                ));
            };
            let variant_name = segment.ident.to_string();
            let (_, variant) = datatype_variant(scrutinee_ty, &variant_name)?;
            let mut seen_fields = BTreeSet::new();
            let mut fields = Vec::with_capacity(struct_pat.fields.len());
            for field in &struct_pat.fields {
                let field_name = match &field.member {
                    syn::Member::Named(name) => name.to_string(),
                    other => {
                        return Err(LoweringError::UnsupportedPattern(format!(
                            "unsupported struct field member '{}'",
                            quote::quote!(#other)
                        )));
                    }
                };
                if !seen_fields.insert(field_name.clone()) {
                    return Err(LoweringError::UnsupportedPattern(format!(
                        "duplicate struct field pattern '{}'",
                        field_name
                    )));
                }
                datatype_field(&variant_name, variant, field_name.as_str())?;
                let binding = match field.pat.as_ref() {
                    syn::Pat::Ident(binding)
                        if binding.by_ref.is_none()
                            && binding.mutability.is_none()
                            && binding.subpat.is_none() =>
                    {
                        Some(binding.ident.to_string())
                    }
                    syn::Pat::Wild(_) => None,
                    other => {
                        return Err(LoweringError::UnsupportedPattern(format!(
                            "unsupported struct field sub-pattern '{}'; use simple identifier bindings or '_'",
                            quote::quote!(#other)
                        )));
                    }
                };
                fields.push(StructPatternField {
                    field_name,
                    binding,
                });
            }
            let has_rest = struct_pat.rest.is_some();
            if !has_rest {
                let missing: Vec<_> = variant
                    .fields
                    .iter()
                    .map(|(field_name, _)| field_name.as_str())
                    .filter(|field_name| !seen_fields.contains(*field_name))
                    .collect();
                if !missing.is_empty() {
                    return Err(LoweringError::UnsupportedPattern(format!(
                        "struct pattern '{}' must mention field(s) {} or use '..'",
                        variant_name,
                        missing.join(", ")
                    )));
                }
            }
            Ok(MatchPattern::Struct {
                variant_name,
                fields,
                has_rest,
            })
        }
        syn::Pat::Wild(_) => Ok(MatchPattern::Wildcard),
        syn::Pat::Tuple(tuple) => {
            // A plain-tuple pattern `(l, r)` destructures the single-variant
            // `"Tuple"` datatype that models a Rust tuple. Reuse the constructor
            // machinery: the `is-Tuple` tester is TOTAL (irrefutable) so the arm is
            // exhaustive over the tuple datatype, and each element binds to the
            // tuple selector `Tuple_i` (`Tuple_0`, `Tuple_1`, …) — the exact
            // field-projection binding, never a havoc value.
            //
            // Admit EXACT-ARITY plain-identifier / `_` elements, plus a single
            // TRAILING `..` rest which binds the LEADING elements and ignores the
            // remainder (mirror `Struct::has_rest`; the arity checks in
            // `extend_env_with_pattern` and `bind_match_pattern_locals` relax to
            // `bindings <= fields` when `has_rest`). A binding AFTER `..` (a
            // middle/back rest) needs a field-index remap and is out of scope, so
            // it fails closed here. Nested, `ref`, `@`, or otherwise non-trivial
            // sub-elements likewise fail closed with the same `UnsupportedPattern`
            // diagnostic as the catch-all.
            let mut bindings = Vec::with_capacity(tuple.elems.len());
            let mut has_rest = false;
            for (index, elem) in tuple.elems.iter().enumerate() {
                match elem {
                    syn::Pat::Rest(_) => {
                        has_rest = true;
                    }
                    syn::Pat::Ident(binding)
                        if binding.by_ref.is_none()
                            && binding.mutability.is_none()
                            && binding.subpat.is_none() =>
                    {
                        if has_rest {
                            return Err(LoweringError::UnsupportedPattern(
                                "unsupported pattern: a binding after `..` (middle/back rest) \
                                 in a tuple pattern is not admitted; only a trailing rest is \
                                 supported"
                                    .into(),
                            ));
                        }
                        bindings.push(binding.ident.to_string());
                    }
                    syn::Pat::Wild(_) => {
                        if has_rest {
                            return Err(LoweringError::UnsupportedPattern(
                                "unsupported pattern: a binding after `..` (middle/back rest) \
                                 in a tuple pattern is not admitted; only a trailing rest is \
                                 supported"
                                    .into(),
                            ));
                        }
                        bindings.push(format!(
                            "{IGNORED_MATCH_BINDING_PREFIX}{TUPLE_VARIANT_NAME}_{index}"
                        ));
                    }
                    _ => {
                        return Err(LoweringError::UnsupportedPattern(
                            "unsupported pattern".into(),
                        ))
                    }
                }
            }
            Ok(MatchPattern::Constructor {
                variant_name: TUPLE_VARIANT_NAME.to_string(),
                bindings,
                has_rest,
            })
        }
        syn::Pat::Or(o) => {
            let subs: Result<Vec<_>, _> = o
                .cases
                .iter()
                .map(|case| lower_pattern(case, scrutinee_ty, current_depth))
                .collect();
            Ok(MatchPattern::Or(subs?))
        }
        syn::Pat::Range(range) => lower_range_pattern(range, scrutinee_ty),
        syn::Pat::Paren(p) => lower_pattern(&p.pat, scrutinee_ty, current_depth),
        _ => Err(LoweringError::UnsupportedPattern(
            "unsupported pattern".into(),
        )),
    }
}

fn lower_range_pattern(
    range: &syn::ExprRange,
    scrutinee_ty: &TrustVcType,
) -> Result<MatchPattern, LoweringError> {
    if !matches!(&range.limits, syn::RangeLimits::Closed(_)) {
        return Err(LoweringError::UnsupportedPattern(
            "only closed inclusive range patterns are supported".into(),
        ));
    }
    if !scrutinee_ty.is_integer() {
        return Err(LoweringError::UnsupportedPattern(
            "range patterns require an integer scrutinee".into(),
        ));
    }
    let start = range.start.as_deref().ok_or_else(|| {
        LoweringError::UnsupportedPattern("range patterns require a literal start bound".into())
    })?;
    let end = range.end.as_deref().ok_or_else(|| {
        LoweringError::UnsupportedPattern("range patterns require a literal end bound".into())
    })?;
    let (start_value, start_suffix) = int_literal_bound(start, "start")?;
    let (end_value, end_suffix) = int_literal_bound(end, "end")?;
    if !start_suffix.is_empty() && !end_suffix.is_empty() && start_suffix != end_suffix {
        return Err(LoweringError::UnsupportedPattern(
            "range pattern bounds must use the same integer suffix".into(),
        ));
    }
    let range_ty = if !start_suffix.is_empty() {
        super::type_from_int_suffix(start_suffix)?
    } else if !end_suffix.is_empty() {
        super::type_from_int_suffix(end_suffix)?
    } else {
        scrutinee_ty.clone()
    };
    if range_ty != scrutinee_ty.clone() {
        return Err(LoweringError::UnsupportedPattern(format!(
            "range pattern type '{}' does not match scrutinee type '{}'",
            range_ty.to_type_string(),
            scrutinee_ty.to_type_string()
        )));
    }
    if start_value > end_value {
        return Err(LoweringError::UnsupportedPattern(
            "empty range patterns are not supported".into(),
        ));
    }
    let case_count = end_value
        .checked_sub(start_value)
        .and_then(|span| span.checked_add(1))
        .ok_or_else(|| {
            LoweringError::UnsupportedPattern("range pattern is too large to expand safely".into())
        })?;
    if case_count > MAX_EXPANDED_RANGE_PATTERN_CASES {
        return Err(LoweringError::UnsupportedPattern(format!(
            "range pattern expands to {case_count} cases, above the supported limit of {MAX_EXPANDED_RANGE_PATTERN_CASES}"
        )));
    }
    Ok(MatchPattern::Or(
        (start_value..=end_value)
            .map(|value| {
                MatchPattern::Lit(TrustVcExpr::IntLit {
                    value,
                    ty: range_ty.clone(),
                })
            })
            .collect(),
    ))
}

fn int_literal_bound<'a>(
    expr: &'a syn::Expr,
    bound_name: &str,
) -> Result<(i128, &'a str), LoweringError> {
    let syn::Expr::Lit(expr_lit) = expr else {
        return Err(LoweringError::UnsupportedPattern(format!(
            "range pattern {bound_name} bound must be an integer literal"
        )));
    };
    let syn::Lit::Int(int_lit) = &expr_lit.lit else {
        return Err(LoweringError::UnsupportedPattern(format!(
            "range pattern {bound_name} bound must be an integer literal"
        )));
    };
    let value = int_lit
        .base10_parse()
        .map_err(|err| LoweringError::InvalidLiteral(err.to_string()))?;
    Ok((value, int_lit.suffix()))
}

fn lower_syn_lit(lit: &syn::Lit) -> Result<TrustVcExpr, LoweringError> {
    match lit {
        syn::Lit::Bool(b) => Ok(TrustVcExpr::BoolLit(b.value)),
        syn::Lit::Int(i) => {
            let v: i128 = i
                .base10_parse()
                .map_err(|e| LoweringError::InvalidLiteral(e.to_string()))?;
            Ok(TrustVcExpr::IntLit {
                value: v,
                ty: super::type_from_int_suffix(i.suffix())?,
            })
        }
        _ => Err(LoweringError::InvalidLiteral(
            "not bool or int in pattern".into(),
        )),
    }
}

fn datatype_variant<'a>(
    scrutinee_ty: &'a TrustVcType,
    variant_name: &str,
) -> Result<(&'a str, &'a DatatypeVariant), LoweringError> {
    let TrustVcType::Datatype { name, variants } = scrutinee_ty else {
        return Err(LoweringError::TypeInference(format!(
            "constructor pattern '{}' requires a datatype scrutinee, got '{}'",
            variant_name,
            scrutinee_ty.to_type_string()
        )));
    };
    let variant = variants
        .iter()
        .find(|variant| variant.name == variant_name)
        .ok_or(LoweringError::TypeInference(format!(
            "unknown datatype variant '{}' for '{}'",
            variant_name, name
        )))?;
    Ok((name.as_str(), variant))
}

fn matches_zero_field_variant(scrutinee_ty: &TrustVcType, variant_name: &str) -> bool {
    matches!(
        datatype_variant(scrutinee_ty, variant_name),
        Ok((_, DatatypeVariant { fields, .. })) if fields.is_empty()
    )
}

fn datatype_field<'a>(
    variant_name: &str,
    variant: &'a DatatypeVariant,
    field_name: &str,
) -> Result<(usize, &'a TrustVcType), LoweringError> {
    variant
        .fields
        .iter()
        .enumerate()
        .find(|(_, (name, _))| name == field_name)
        .map(|(index, (_, field_ty))| (index, field_ty))
        .ok_or_else(|| {
            LoweringError::UnsupportedPattern(format!(
                "unknown field '{}' in struct pattern '{}'",
                field_name, variant_name
            ))
        })
}
