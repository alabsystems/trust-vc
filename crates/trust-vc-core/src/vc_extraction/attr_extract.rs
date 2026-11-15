// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::error::{TrustVcError, TrustVcResult};
use crate::vc::{ProofObligation, SolverMode, VerificationContext};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{Expr, FnArg, Ident, Lit, Pat, Signature, Token, Type};

const SPEC_RETURNS_ERROR: &str = "spec functions cannot have `returns` clause";
const RETURNS_TYPE_MISMATCH_ERROR: &str =
    "type of `returns` clause does not match function return type";

struct ContractClause {
    name: Ident,
    args: Vec<Expr>,
}

impl Parse for ContractClause {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        let args = Punctuated::<Expr, Token![,]>::parse_terminated(&content)?;
        Ok(Self {
            name,
            args: args.into_iter().collect(),
        })
    }
}

/// Parse the parenthesized expression carried by a contract attribute
/// (`#[requires(..)]`, `#[ensures(..)]`, `#[recommends(..)]`, `#[returns(..)]`),
/// normalizing Verus surface syntax that plain `syn` rejects.
///
/// In particular this accepts the bar-delimited quantifier closure form that is
/// Verus's canonical surface — `exists |n: T| body` / `forall |n: T| body` —
/// lowering it to the call form `exists(|n: T| body)` so it parses identically
/// to the already-supported call form. Chained comparisons are likewise
/// rewritten into pairwise conjunctions.
fn parse_contract_attr_expr(attr: &syn::Attribute) -> syn::Result<Expr> {
    let syn::Meta::List(meta_list) = &attr.meta else {
        return Err(syn::Error::new_spanned(
            attr,
            "contract attribute must use parenthesized form, e.g. `#[ensures(expr)]`",
        ));
    };
    crate::chained_comparisons::parse_expr_tokens_with_chains(meta_list.tokens.clone())
}

/// Like [`parse_contract_attr_expr`], but additionally collects the clause's
/// `#[verifier::proof_note("…")]` / `custom_err` label (Verus basic.rs
/// FAMILY C). Labels are pooled from BOTH clause-level attachment positions —
/// leading INNER attrs `#![…]` in the attribute tokens (the Verus surface
/// spelling, normalized upstream by `builtin_macros/src/syntax.rs:3710-3724`)
/// and leading OUTER attrs on the parsed clause expression — and the upstream
/// at-most-one rule is enforced verbatim. Purely additive: the inner-attr
/// token shape previously ALWAYS failed the `Expr` parse fail-closed, so no
/// legal clause changes meaning; the collected attrs are STRIPPED so the
/// rendered condition string is unchanged.
fn parse_contract_attr_expr_noted(
    attr: &syn::Attribute,
    on_parse_err: impl FnOnce(syn::Error) -> TrustVcError,
) -> TrustVcResult<(Expr, Option<crate::proof_note::ProofNoteLabel>)> {
    let syn::Meta::List(meta_list) = &attr.meta else {
        return Err(on_parse_err(syn::Error::new_spanned(
            attr,
            "contract attribute must use parenthesized form, e.g. `#[ensures(expr)]`",
        )));
    };
    let (mut labels, rest) =
        crate::proof_note::peel_leading_inner_proof_note_attrs(meta_list.tokens.clone())?;
    let mut expr =
        crate::chained_comparisons::parse_expr_tokens_with_chains(rest).map_err(on_parse_err)?;
    labels.extend(crate::proof_note::take_leading_proof_note_labels(
        &mut expr,
    )?);
    let label = crate::proof_note::at_most_one_proof_note(labels)?;
    Ok((expr, label))
}

fn parse_contract_clauses(attr: &syn::Attribute) -> TrustVcResult<Vec<ContractClause>> {
    attr.parse_args_with(Punctuated::<ContractClause, Token![,]>::parse_terminated)
        .map(|clauses| clauses.into_iter().collect())
        .map_err(|source| TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: format!(
                "Failed to parse #[contract] attribute: {} — \
                 this would silently drop the contract",
                source
            ),
        })
}

fn ensure_nonempty_clause(clause: &ContractClause) -> TrustVcResult<()> {
    if clause.args.is_empty() {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: format!(
                "{}() must have at least one argument in #[contract]",
                clause.name
            ),
        });
    }
    Ok(())
}

fn returns_clause_ident(clause: &ContractClause) -> TrustVcResult<String> {
    if clause.args.len() != 1 {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: "returns() takes exactly one identifier in #[contract]".into(),
        });
    }

    let Some(expr) = clause.args.first() else {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: "returns() takes exactly one identifier in #[contract]".into(),
        });
    };
    returns_expr_ident(
        expr,
        "returns() argument must be a simple identifier in #[contract]",
    )
}

fn returns_expr_ident_opt(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(expr_path) if expr_path.qself.is_none() => {
            expr_path.path.get_ident().map(ToString::to_string)
        }
        _ => None,
    }
}

fn returns_expr_ident(expr: &Expr, detail: &'static str) -> TrustVcResult<String> {
    returns_expr_ident_opt(expr).ok_or_else(|| TrustVcError::Encoding {
        context: "extract contract attributes",
        detail: detail.into(),
    })
}

fn tuple_return_names_expr(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Tuple(tuple)
            if !tuple.elems.is_empty() && tuple.elems.iter().all(|elem| {
                returns_expr_ident_opt(elem).is_some()
            })
    )
}

fn direct_returns_condition(sig: Option<&Signature>, expr: &Expr) -> TrustVcResult<Option<String>> {
    validate_direct_returns_literal_type(sig, expr)?;

    if let Some(ident) = direct_shared_reference_ident_expr(sig, expr) {
        let Some(sig) = sig else {
            return Err(TrustVcError::Encoding {
                context: "extract contract attributes",
                detail: format!(
                    "unsupported direct #[returns] shared-reference identifier `{ident}`: \
                     missing function signature context"
                ),
            });
        };
        validate_supported_direct_shared_reference_ident(sig, &ident)?;
        return Ok(Some(format!(
            "result == ({})",
            super::extract_expr_string(expr)
        )));
    }

    if returns_expr_ident_opt(expr).is_some() {
        return Ok(None);
    }

    if tuple_return_names_expr(expr) {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: "tuple #[returns] bindings are not supported by file VC extraction".into(),
        });
    }

    Ok(Some(format!(
        "result == ({})",
        super::extract_expr_string(expr)
    )))
}

fn validate_direct_returns_literal_type(sig: Option<&Signature>, expr: &Expr) -> TrustVcResult<()> {
    let Some(sig) = sig else {
        return Ok(());
    };
    let Some(expected) = function_return_type_name(sig) else {
        return Ok(());
    };
    let Some(actual) = literal_expr_type_name(expr) else {
        return Ok(());
    };

    if expected != actual {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: RETURNS_TYPE_MISMATCH_ERROR.into(),
        });
    }

    Ok(())
}

fn primitive_type_name(ty: &Type) -> Option<&'static str> {
    match ty {
        Type::Path(type_path) if type_path.qself.is_none() => {
            let segment = type_path.path.segments.last()?;
            match segment.ident.to_string().as_str() {
                "bool" => Some("bool"),
                "char" => Some("char"),
                "i8" => Some("i8"),
                "i16" => Some("i16"),
                "i32" => Some("i32"),
                "i64" => Some("i64"),
                "i128" => Some("i128"),
                "isize" => Some("isize"),
                "u8" => Some("u8"),
                "u16" => Some("u16"),
                "u32" => Some("u32"),
                "u64" => Some("u64"),
                "u128" => Some("u128"),
                "usize" => Some("usize"),
                "f32" => Some("f32"),
                "f64" => Some("f64"),
                _ => None,
            }
        }
        Type::Tuple(tuple) if tuple.elems.is_empty() => Some("()"),
        Type::Paren(paren) => primitive_type_name(&paren.elem),
        Type::Group(group) => primitive_type_name(&group.elem),
        _ => None,
    }
}

fn function_return_type_name(sig: &Signature) -> Option<&'static str> {
    match &sig.output {
        syn::ReturnType::Default => Some("()"),
        syn::ReturnType::Type(_, ty) => primitive_type_name(ty),
    }
}

fn literal_expr_type_name(expr: &Expr) -> Option<&'static str> {
    match expr {
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            Lit::Bool(_) => Some("bool"),
            Lit::Char(_) => Some("char"),
            Lit::Int(lit) => match lit.suffix() {
                "i8" => Some("i8"),
                "i16" => Some("i16"),
                "i32" => Some("i32"),
                "i64" => Some("i64"),
                "i128" => Some("i128"),
                "isize" => Some("isize"),
                "u8" => Some("u8"),
                "u16" => Some("u16"),
                "u32" => Some("u32"),
                "u64" => Some("u64"),
                "u128" => Some("u128"),
                "usize" => Some("usize"),
                _ => None,
            },
            Lit::Float(lit) => match lit.suffix() {
                "f32" => Some("f32"),
                "f64" => Some("f64"),
                _ => None,
            },
            _ => None,
        },
        Expr::Tuple(tuple) if tuple.elems.is_empty() => Some("()"),
        Expr::Paren(paren) => literal_expr_type_name(&paren.expr),
        Expr::Group(group) => literal_expr_type_name(&group.expr),
        _ => None,
    }
}

fn direct_shared_reference_ident_expr(sig: Option<&Signature>, expr: &Expr) -> Option<String> {
    let sig = sig?;
    match expr {
        Expr::Path(expr_path) if expr_path.qself.is_none() => {
            let ident = expr_path.path.get_ident()?;
            (signature_shared_reference_referent(sig).is_some()
                && shared_reference_param_referent(sig, ident).is_some())
            .then(|| ident.to_string())
        }
        Expr::Paren(paren) => direct_shared_reference_ident_expr(Some(sig), &paren.expr),
        Expr::Group(group) => direct_shared_reference_ident_expr(Some(sig), &group.expr),
        _ => None,
    }
}

fn validate_supported_direct_shared_reference_ident(
    sig: &Signature,
    ident: &str,
) -> TrustVcResult<()> {
    let Some(return_referent) = signature_shared_reference_referent(sig) else {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: format!(
                "unsupported direct #[returns] shared-reference identifier `{ident}`: \
                 function return type is not a shared reference"
            ),
        });
    };
    let Some(param_referent) = shared_reference_param_referent_by_name(sig, ident) else {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: format!(
                "unsupported direct #[returns] shared-reference identifier `{ident}`: \
                 parameter is not a shared reference"
            ),
        });
    };

    if !supported_direct_shared_reference_referent(return_referent)
        || !supported_direct_shared_reference_referent(param_referent)
    {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: format!(
                "unsupported direct #[returns] shared-reference identifier `{ident}`: \
                 only bool and integer referents are supported by file VC extraction"
            ),
        });
    }

    if compact_type_string(return_referent) != compact_type_string(param_referent) {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: format!(
                "unsupported direct #[returns] shared-reference identifier `{ident}`: \
                 return and parameter referent types must match"
            ),
        });
    }

    Ok(())
}

fn signature_shared_reference_referent(sig: &Signature) -> Option<&Type> {
    match &sig.output {
        syn::ReturnType::Type(_, ty) => shared_reference_referent_type(ty),
        syn::ReturnType::Default => None,
    }
}

fn shared_reference_param_referent<'a>(sig: &'a Signature, ident: &Ident) -> Option<&'a Type> {
    shared_reference_param_referent_by_name(sig, &ident.to_string())
}

fn shared_reference_param_referent_by_name<'a>(
    sig: &'a Signature,
    ident: &str,
) -> Option<&'a Type> {
    sig.inputs.iter().find_map(|input| {
        let FnArg::Typed(pat_type) = input else {
            return None;
        };
        (pat_ident(&pat_type.pat).is_some_and(|param| param == ident))
            .then(|| shared_reference_referent_type(&pat_type.ty))
            .flatten()
    })
}

fn shared_reference_referent_type(ty: &Type) -> Option<&Type> {
    match ty {
        Type::Reference(reference) if reference.mutability.is_none() => Some(&reference.elem),
        Type::Paren(paren) => shared_reference_referent_type(&paren.elem),
        Type::Group(group) => shared_reference_referent_type(&group.elem),
        _ => None,
    }
}

fn pat_ident(pat: &Pat) -> Option<&Ident> {
    match pat {
        Pat::Ident(pat_ident) => Some(&pat_ident.ident),
        Pat::Type(pat_type) => pat_ident(&pat_type.pat),
        Pat::Reference(pat_ref) => pat_ident(&pat_ref.pat),
        _ => None,
    }
}

fn supported_direct_shared_reference_referent(ty: &Type) -> bool {
    matches!(
        compact_type_string(ty).as_str(),
        "bool"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
    )
}

fn compact_type_string(ty: &Type) -> String {
    quote!(#ty).to_string().replace(' ', "")
}

fn set_return_binding(binding: &mut Option<String>, name: String) -> TrustVcResult<()> {
    if binding.replace(name).is_some() {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: "duplicate returns binding in contract attributes".into(),
        });
    }
    Ok(())
}

fn has_spec_attr(attrs: &[syn::Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| super::path_last_segment(attr.path()).as_deref() == Some("spec"))
}

fn reject_returns_on_spec(attrs: &[syn::Attribute]) -> TrustVcResult<()> {
    if !has_spec_attr(attrs) {
        return Ok(());
    }

    for attr in attrs {
        #[allow(clippy::collapsible_match)]
        match super::path_last_segment(attr.path()).as_deref() {
            Some("returns") => {
                return Err(TrustVcError::Encoding {
                    context: "extract contract attributes",
                    detail: SPEC_RETURNS_ERROR.into(),
                });
            }
            Some("contract") => {
                if parse_contract_clauses(attr)?
                    .iter()
                    .any(|clause| clause.name == "returns")
                {
                    return Err(TrustVcError::Encoding {
                        context: "extract contract attributes",
                        detail: SPEC_RETURNS_ERROR.into(),
                    });
                }
            }
            _ => {}
        }
    }

    Ok(())
}

/// Verus rejects a return-value binding whose name collides with any
/// parameter binding at MACRO expansion (`builtin_macros/src/syntax.rs`
/// `check_return_idents` / `check_verus_return_idents`): every identifier
/// bound by the return pattern is intersected with every identifier bound by
/// a typed-parameter pattern (nested patterns included; the `self` receiver
/// is skipped), and any overlap is a compile error for the whole file.
/// Upstream witnesses: basic.rs `test_ensures_ret_val_collision`
/// (`fn f(k: u32, n: u32) -> ((_, n): (u32, u32))`) and
/// `test_fail_return_value_parameter_same_name` (`fn foo(x: u64) -> (x: bool)`)
/// — "return value name collides with a parameter name". Purely syntactic
/// upstream, so a perfect syn-frontend fit. Reject-only: it fires only when an
/// EXPLICIT returns binding names a parameter (both witness shapes already
/// errored here with an internal "Variable 'x' already declared" message);
/// the implicit `result` variable and non-colliding bindings are untouched.
/// Collect every bound ident from a returns-tuple expression, recursing
/// through nested tuples — mirrors upstream `check_return_idents`, which
/// walks NESTED return patterns (`(r, (b, c))` binds `r`, `b`, and `c`).
fn collect_returns_tuple_idents(tuple: &syn::ExprTuple, names: &mut Vec<String>) {
    for elem in &tuple.elems {
        if let Expr::Tuple(nested) = elem {
            collect_returns_tuple_idents(nested, names);
        } else if let Some(name) = returns_expr_ident_opt(elem) {
            names.push(name);
        }
    }
}

fn reject_return_binding_param_collision(
    sig: Option<&Signature>,
    return_names: &[String],
) -> TrustVcResult<()> {
    let Some(sig) = sig else {
        return Ok(());
    };
    let mut param_names = Vec::new();
    for input in &sig.inputs {
        // FnArg::Receiver (`self`) is skipped, matching upstream.
        if let FnArg::Typed(pat_type) = input {
            super::collect_pat_binding_names(&pat_type.pat, &mut param_names);
        }
    }
    if return_names
        .iter()
        .any(|name| param_names.iter().any(|param| param == name))
    {
        return Err(TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: "return value name collides with a parameter name".to_string(),
        });
    }
    Ok(())
}

pub(super) fn extract_return_binding(
    attrs: &[syn::Attribute],
    sig: Option<&Signature>,
) -> TrustVcResult<Option<String>> {
    reject_returns_on_spec(attrs)?;

    let mut binding = None;

    for attr in attrs {
        match super::path_last_segment(attr.path()).as_deref() {
            Some("returns") => {
                let expr =
                    parse_contract_attr_expr(attr).map_err(|source| TrustVcError::Encoding {
                        context: "extract contract attributes",
                        detail: format!(
                            "Failed to parse #[returns] attribute: {} — \
                         this would silently drop the return binding",
                            source
                        ),
                    })?;
                if direct_shared_reference_ident_expr(sig, &expr).is_some() {
                    // Returns-CONDITION reading (legal Verus `returns x`
                    // clause on a shared-reference param), not a binding —
                    // the collision rule does not apply.
                    direct_returns_condition(sig, &expr)?;
                } else if let Some(name) = returns_expr_ident_opt(&expr) {
                    reject_return_binding_param_collision(sig, std::slice::from_ref(&name))?;
                    set_return_binding(&mut binding, name)?;
                } else if let Expr::Tuple(tuple) = &expr {
                    // Tuple return-name patterns (`((_, n): (u32, u32))`
                    // upstream): scan ALL bound idents for a parameter
                    // collision FIRST — upstream fires the collision error at
                    // macro expansion before anything else — then fall back
                    // to the existing tuple-unsupported rejection. The scan
                    // recurses through NESTED tuples (`(r, (b, c))`) because
                    // upstream's check_return_idents walks nested patterns.
                    let mut names: Vec<String> = Vec::new();
                    collect_returns_tuple_idents(tuple, &mut names);
                    reject_return_binding_param_collision(sig, &names)?;
                    if tuple_return_names_expr(&expr) {
                        return Err(TrustVcError::Encoding {
                            context: "extract contract attributes",
                            detail:
                                "tuple #[returns] bindings are not supported by file VC extraction"
                                    .into(),
                        });
                    }
                }
            }
            Some("contract") => {
                for clause in parse_contract_clauses(attr)? {
                    if clause.name == "returns" {
                        let name = returns_clause_ident(&clause)?;
                        reject_return_binding_param_collision(sig, std::slice::from_ref(&name))?;
                        set_return_binding(&mut binding, name)?;
                    }
                }
            }
            _ => {}
        }
    }

    Ok(binding)
}

pub(super) fn has_direct_returns_postcondition(
    attrs: &[syn::Attribute],
    sig: Option<&Signature>,
) -> TrustVcResult<bool> {
    reject_returns_on_spec(attrs)?;

    for attr in attrs {
        if super::path_last_segment(attr.path()).as_deref() != Some("returns") {
            continue;
        }
        let expr = parse_contract_attr_expr(attr).map_err(|source| TrustVcError::Encoding {
            context: "extract contract attributes",
            detail: format!(
                "Failed to parse #[returns] attribute: {} — \
                         this would silently drop the return postcondition",
                source
            ),
        })?;
        if direct_returns_condition(sig, &expr)?.is_some() {
            return Ok(true);
        }
    }

    Ok(false)
}

fn extract_contract_clause(
    clause: &ContractClause,
    vc: &mut VerificationContext,
    ambient_solver_mode: Option<SolverMode>,
) -> TrustVcResult<()> {
    match clause.name.to_string().as_str() {
        "requires" => {
            ensure_nonempty_clause(clause)?;
            for expr in &clause.args {
                // Per-clause proof-note pooling: each comma-separated clause
                // arg carries its own label (leading OUTER attr form; the
                // inner `#![…]` form inside a grouped #[contract] still fails
                // the Punctuated<Expr> parse closed, unchanged).
                let mut expr = expr.clone();
                let labels = crate::proof_note::take_leading_proof_note_labels(&mut expr)?;
                let label = crate::proof_note::at_most_one_proof_note(labels)?;
                let condition = super::extract_expr_string(&expr);
                vc.push_obligation(
                    with_ambient_solver_mode(
                        ProofObligation::assume("precondition", &condition),
                        ambient_solver_mode,
                    )
                    .with_proof_note(label),
                );
            }
        }
        "ensures" => {
            ensure_nonempty_clause(clause)?;
            for expr in &clause.args {
                let mut expr = expr.clone();
                let labels = crate::proof_note::take_leading_proof_note_labels(&mut expr)?;
                let label = crate::proof_note::at_most_one_proof_note(labels)?;
                let condition = super::extract_expr_string(&expr);
                vc.push_obligation(
                    with_ambient_solver_mode(
                        ProofObligation::assert("postcondition", &condition),
                        ambient_solver_mode,
                    )
                    .with_proof_note(label),
                );
            }
        }
        "recommends" => {
            ensure_nonempty_clause(clause)?;
            for expr in &clause.args {
                // Pool-check only; a recommends label is never attached (soft
                // warnings must not enter the proof-note error channel).
                let mut expr = expr.clone();
                let labels = crate::proof_note::take_leading_proof_note_labels(&mut expr)?;
                let _label = crate::proof_note::at_most_one_proof_note(labels)?;
                let condition = super::extract_expr_string(&expr);
                vc.push_obligation(with_ambient_solver_mode(
                    ProofObligation::recommends("recommendation", &condition),
                    ambient_solver_mode,
                ));
            }
        }
        "returns" => {
            returns_clause_ident(clause)?;
        }
        "decreases" => ensure_nonempty_clause(clause)?,
        other => {
            return Err(TrustVcError::Encoding {
                context: "extract contract attributes",
                detail: format!("unknown contract clause `{other}` in #[contract]"),
            });
        }
    }

    Ok(())
}

fn with_ambient_solver_mode(
    obligation: ProofObligation,
    ambient_solver_mode: Option<SolverMode>,
) -> ProofObligation {
    match ambient_solver_mode {
        Some(mode) => obligation.with_solver_mode(mode),
        None => obligation,
    }
}

/// Every attribute name that may legally appear under an explicit `trust_vc::`
/// namespace on a function the file-VC lane verifies.
///
/// SOUNDNESS (FV-2): the outer attribute match below is an ALLOWLIST of the
/// clauses this pass consumes, and it used to end in `_ => {}`. That arm also
/// swallowed `trust_vc::`-namespaced attributes it did not recognize — so
/// `#[trust_vc::ghost_ensures(result > 100)]` or a bare typo like
/// `#[trust_vc::ensurez(..)]` DISAPPEARED, and a function whose only
/// postcondition was the dropped clause verified vacuously. Inside a grouped
/// `#[contract(..)]` the identical unknown clause was already a hard error
/// (`extract_contract_clause`'s `other =>` arm), so the two paths disagreed.
/// The one structural floor, `ValidationError::OnlyAssumptions`, is
/// per-CONTEXT — it fires only when EVERY assertion lane is empty — so a
/// dropped clause sitting next to a surviving `#[ensures(..)]` was invisible.
///
/// The compiled lane is not exposed: an attribute that is not one of the 27
/// real `#[proc_macro_attribute]` exports is a rustc error long before
/// extraction. The file-VC lane (`verify_function_from_file` /
/// `cargo trust-vc check`, the corpus evidence channel) never compiles the
/// source, so this list is the only thing standing between a misspelled clause
/// and a silent proof hole.
///
/// Membership means "a name the toolchain recognizes somewhere", NOT "consumed
/// here" — most entries are read by other passes (`mode_attrs`, `spec_expand`,
/// `trait_contracts`, …) or are inert markers, and they must keep passing
/// through this pass untouched. Names that are deliberately ABSENT are the
/// unsupported spellings the toolchain already documents as such:
/// `verified`, `ghost`, `lemma_cache`, `loop_invariant`, `invariant`,
/// `rational`, `trace_encoding` (the exact forbidden set asserted by
/// `crates/trust-vc/tests/doc_api_syntax.rs`), plus `no_unwind` and `safe_api`,
/// whose capability-audit rows record them as MISSING with enforcement
/// undetermined — precisely the "silently dropped looks identical to enforced"
/// hazard this gate closes.
///
/// Adding a name here is a soundness decision: do it only when the attribute is
/// genuinely honoured by some pass.
pub(super) const KNOWN_TRUST_VC_ATTRIBUTES: &[&str] = &[
    // --- clause attributes consumed by this pass ---
    "requires",
    "ensures",
    "recommends",
    "returns",
    "contract",
    // --- the 27 real `#[proc_macro_attribute]` exports (crates/trust-vc) ---
    "action",
    "all_triggers",
    "allow_in_spec",
    "auto_trigger",
    "broadcast",
    "broadcast_group",
    "decreases",
    "external",
    "external_body",
    "inline",
    "liveness",
    "memoize",
    "opaque",
    "opens_invariants",
    "proof",
    "protocol",
    "safety",
    "spec",
    "spec_mode",
    "trait_impl",
    "trait_spec",
    "trigger",
    "verifier",
    "via_fn",
    "when_used_as_spec",
    // --- names honoured by other passes / injected by desugarings ---
    // `default_ensures` — trait-method defaulted postcondition (trait_contracts,
    // `extern_spec_helpers::forbid_default_ensures` rejects it off-trait).
    "default_ensures",
    // `proof_note` / `custom_err` — clause labels (crate::proof_note).
    "proof_note",
    "custom_err",
    // `rlimit` — per-function solver budget (crate::mode_attrs).
    "rlimit",
    // `uninterp` — injected by `crate::tracked_syntax` via `parse_quote!`.
    "uninterp",
];

/// True when the item carries a TRUSTED-BOUNDARY marker —
/// `#[trust_vc::external_body]` or `#[trust_vc::external]` (and the
/// `#[verifier::…]` spellings, matched here on the last segment).
///
/// SOUNDNESS-CRITICAL (H14, a trust-boundary breach). The braces of such an item
/// hold a PLACEHOLDER: the real implementation is foreign, or lives elsewhere,
/// and the text only exists so the item compiles. Trust's unified compilation is
/// what makes an ORDINARY exec callee's body legitimately visible to its caller,
/// and definitional exec bodies stay the default here — but no amount of
/// whole-program visibility makes a stub the thing that runs. So every
/// `__body_axiom_*` publisher consults this predicate and declines: the callee is
/// left as an opaque UF carrying its DECLARED contract (`#[requires]` /
/// `#[ensures]`), which is what a trusted declaration promises and the only thing
/// a caller may assume about it.
///
/// Last-segment matching is deliberately WIDE: `#[verifier::external_body]` and
/// any other namespace spelling also decline. Over-declining costs completeness
/// on the callee's body; under-declining publishes a placeholder as a fact.
pub(crate) fn has_external_trusted_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "external" || segment.ident == "external_body")
    })
}

/// True when `path` explicitly names the `trust_vc` namespace ahead of its
/// final segment — `#[trust_vc::foo]`, `#[::trust_vc::foo]`,
/// `#[crate::trust_vc::foo]`.
///
/// NARROWNESS: a single-segment path (`#[test]`, `#[inline]`, `#[derive]`, the
/// `#[doc = ".."]` a doc comment lowers to) is never namespaced, and neither is
/// a foreign namespace (`#[verifier::external_body]`, `#[serde(..)]`,
/// `#[tokio::main]`). Those keep falling through silently, exactly as before.
/// Only an author who reached for `trust_vc::` and misspelled the clause is
/// caught.
fn is_trust_vc_namespaced(path: &syn::Path) -> bool {
    let n = path.segments.len();
    n >= 2
        && path
            .segments
            .iter()
            .take(n - 1)
            .any(|s| s.ident == "trust_vc")
}

/// Reject an unrecognized `trust_vc::`-namespaced attribute instead of dropping
/// it. See [`KNOWN_TRUST_VC_ATTRIBUTES`] for why silence is unsound here.
pub(crate) fn reject_unknown_trust_vc_attribute(attr: &syn::Attribute) -> TrustVcResult<()> {
    if !is_trust_vc_namespaced(attr.path()) {
        return Ok(());
    }
    let Some(name) = super::path_last_segment(attr.path()) else {
        return Ok(());
    };
    if KNOWN_TRUST_VC_ATTRIBUTES.contains(&name.as_str()) {
        return Ok(());
    }
    Err(TrustVcError::Encoding {
        context: "extract contract attributes",
        detail: format!(
            "unknown trust_vc attribute `#[trust_vc::{name}]` — declining rather \
             than silently dropping it, because a discarded clause would leave \
             the function with no obligation and verify vacuously"
        ),
    })
}

/// Extract standalone and grouped contract attributes.
pub(super) fn extract_contract_attributes(
    attrs: &[syn::Attribute],
    vc: &mut VerificationContext,
    ambient_solver_mode: Option<SolverMode>,
    sig: Option<&Signature>,
) -> TrustVcResult<()> {
    reject_returns_on_spec(attrs)?;

    // Every obligation raised below belongs to the CLAUSE ATTRIBUTE it is read
    // from, not to any statement: upstream Verus marks a failing postcondition
    // on the `ensures` line itself (`#[trust_vc::ensures(x * z < y * z)] //
    // FAILS`), so that is the line this lane must report. Parked as the ambient
    // location per attribute and cleared on the way out, so nothing raised
    // after this loop inherits the last clause's line.
    let enclosing = vc.ambient_source_location().cloned();
    let result = extract_contract_attributes_located(attrs, vc, ambient_solver_mode, sig);
    vc.replace_ambient_source_location(enclosing);
    result
}

fn extract_contract_attributes_located(
    attrs: &[syn::Attribute],
    vc: &mut VerificationContext,
    ambient_solver_mode: Option<SolverMode>,
    sig: Option<&Signature>,
) -> TrustVcResult<()> {
    for attr in attrs {
        let attr_name = super::path_last_segment(attr.path());
        vc.replace_ambient_source_location(crate::SourceLocation::from_span(attr.span()));

        match attr_name.as_deref() {
            Some("requires") => {
                let (expr, label) =
                    parse_contract_attr_expr_noted(attr, |source| TrustVcError::Encoding {
                        context: "extract contract attributes",
                        detail: format!(
                            "Failed to parse #[requires] attribute: {} — \
                         this would silently drop the precondition",
                            source
                        ),
                    })?;
                let condition = super::extract_expr_string(&expr);
                vc.push_obligation(
                    with_ambient_solver_mode(
                        ProofObligation::assume("precondition", &condition),
                        ambient_solver_mode,
                    )
                    // A requires-clause label never fails HERE (the callee
                    // assumes its own precondition); it rides the obligation
                    // so the sibling-contract discharge can attach it to the
                    // caller-side `__call_requires_*` obligation.
                    .with_proof_note(label),
                );
            }
            Some("ensures") => {
                let (expr, label) =
                    parse_contract_attr_expr_noted(attr, |source| TrustVcError::Encoding {
                        context: "extract contract attributes",
                        detail: format!(
                            "Failed to parse #[ensures] attribute: {} — \
                         this would silently drop the postcondition",
                            source
                        ),
                    })?;
                let condition = super::extract_expr_string(&expr);
                vc.push_obligation(
                    with_ambient_solver_mode(
                        ProofObligation::assert("postcondition", &condition),
                        ambient_solver_mode,
                    )
                    .with_proof_note(label),
                );
            }
            Some("recommends") => {
                // Labels are still POOLED (the at-most-one rule fires) but a
                // single label is deliberately NOT attached: recommends
                // failures are soft warnings upstream and must never be
                // upgraded to the proof-note error channel.
                let (expr, _label) =
                    parse_contract_attr_expr_noted(attr, |source| TrustVcError::Encoding {
                        context: "extract contract attributes",
                        detail: format!(
                            "Failed to parse #[recommends] attribute: {} — \
                         this would silently drop the recommendation",
                            source
                        ),
                    })?;
                let condition = super::extract_expr_string(&expr);
                vc.push_obligation(with_ambient_solver_mode(
                    ProofObligation::recommends("recommendation", &condition),
                    ambient_solver_mode,
                ));
            }
            Some("returns") => {
                let expr =
                    parse_contract_attr_expr(attr).map_err(|source| TrustVcError::Encoding {
                        context: "extract contract attributes",
                        detail: format!(
                            "Failed to parse #[returns] attribute: {} — \
                         this would silently drop the return postcondition",
                            source
                        ),
                    })?;
                if let Some(condition) = direct_returns_condition(sig, &expr)? {
                    vc.push_obligation(with_ambient_solver_mode(
                        ProofObligation::assert("postcondition", &condition),
                        ambient_solver_mode,
                    ));
                }
            }
            Some("contract") => {
                let clauses = parse_contract_clauses(attr)?;
                let mut seen_returns = false;
                let mut seen_decreases = false;
                for clause in &clauses {
                    match clause.name.to_string().as_str() {
                        "returns" => {
                            if seen_returns {
                                return Err(TrustVcError::Encoding {
                                    context: "extract contract attributes",
                                    detail: "duplicate returns clause in #[contract]".into(),
                                });
                            }
                            seen_returns = true;
                        }
                        "decreases" => {
                            if seen_decreases {
                                return Err(TrustVcError::Encoding {
                                    context: "extract contract attributes",
                                    detail: "duplicate decreases clause in #[contract]".into(),
                                });
                            }
                            seen_decreases = true;
                        }
                        _ => {}
                    }
                    extract_contract_clause(clause, vc, ambient_solver_mode)?;
                }
            }
            // FV-2: this arm used to be a bare `_ => {}`. It is the fall-through
            // for every attribute this pass does not consume — which is correct
            // for ordinary Rust and foreign namespaces, but was a silent DROP
            // for an unrecognized `trust_vc::` clause. Make the standalone path
            // agree with the grouped `#[contract(..)]` path, which already
            // hard-errors on an unknown clause name.
            _ => reject_unknown_trust_vc_attribute(attr)?,
        }
    }

    Ok(())
}
