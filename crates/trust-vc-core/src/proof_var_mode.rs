//! Proof-mode VARIABLES inside `assert … by` / `assert forall … by` blocks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Upstream parity target: `rust_verify_test/tests/assert_forall_by.rs`
//! `test_assertby1_fail3`, `test_forallstmt1_fail3` (both REJECTED with the
//! verbatim message `expression has mode spec, expected mode proof`) and the
//! third fn of `test_forallstmt1` (`forallstmt_proof_var_allowed_as_spec`, the
//! POSITIVE counterpart, which must VERIFY).
//!
//! ## The Verus rule, verbatim
//!
//! Two Verus facts compose into the rule this module implements.
//!
//! 1. **Parameter modes** (`rust_verify/src/attributes.rs`):
//!    ```text
//!    pub(crate) fn get_var_mode(function_mode: Mode, attrs: &[Attribute]) -> Mode {
//!        let default_mode = if function_mode == Mode::Proof { Mode::Spec } else { function_mode };
//!        get_mode(default_mode, attrs)
//!    }
//!    ```
//!    So in a `proof fn`, an un-annotated parameter is **spec**-mode; `tracked p`
//!    (== `#[verifier::proof] p`) makes it **proof**-mode. In an `exec fn`, an
//!    un-annotated parameter is exec-mode and `#[verifier::proof] p` is
//!    proof-mode.
//!
//! 2. **By-blocks demote proof vars to spec** (`vir/src/modes.rs`, `ExprX::AssertBy`):
//!    ```text
//!    // REVIEW: we could allow proof vars when vars.len() == 0,
//!    // but we'd have to implement the proper lifetime checking in erase.rs
//!    let mut typing = typing.push_in_forall_stmt(true);
//!    ```
//!    and, on every variable read,
//!    ```text
//!    if typing.in_forall_stmt || typing.in_proof_in_spec || typing.in_pure {
//!        coerced_mode = Mode::Spec;
//!    }
//!    ```
//!    `in_forall_stmt` is pushed for BOTH `assert(..) by { .. }` and
//!    `assert forall|..| .. by { .. }` (the quoted REVIEW comment is precisely
//!    about the `vars.len() == 0` — i.e. plain assert-by — case), which is why
//!    upstream rejects the plain-assert flavour too.
//!
//! Composing: inside a by-block a proof-mode variable READS at mode `spec`.
//! Passing it to a parameter that expects mode `proof` violates Verus's
//! `mode_le(actual, expected)` and raises
//! `expression has mode spec, expected mode proof`
//! (`vir/src/modes.rs`, `check_expr_has_mode`). Passing it where mode `spec` is
//! expected — upstream's `no_consume(x: bool)`, a spec-mode parameter of a proof
//! fn — is fine, which is the positive case.
//!
//! ## Scope (deliberately narrow, and fail-closed)
//!
//! This module implements exactly the instance above: a call, inside an
//! `assert_by!` / `assert_forall_by!` proof block, that passes a proof-mode
//! PARAMETER of the enclosing function to a proof-mode (`tracked`) parameter of
//! the callee. It is a *rejection-only* rule — it can never make a program
//! verify that did not already, so it cannot introduce unsoundness. It is not a
//! full linearity/affinity checker, and it does not model proof-mode locals
//! (`let tracked x = ..`); those remain future work and simply are not rejected
//! here.

use crate::error::{TrustVcError, TrustVcResult};
use crate::mode::{FunctionMode, VarMode};
use std::collections::BTreeMap;
use syn::visit::Visit;

/// Mode of every parameter of one function, in declaration order.
type ParamModes = Vec<VarMode>;

/// Verus's `get_var_mode`: the default mode of a parameter of a function whose
/// mode is `function_mode`, before any parameter-level attribute is applied.
fn default_param_mode(function_mode: FunctionMode) -> VarMode {
    match function_mode {
        // proof fn params default to SPEC mode (Verus `get_var_mode`).
        FunctionMode::Proof | FunctionMode::Spec => VarMode::Ghost,
        FunctionMode::Exec => VarMode::Exec,
    }
}

/// Reads an explicit parameter-level mode attribute.
///
/// Recognized spellings (all equivalent to Verus's `#[verifier::proof]` /
/// `#[verifier::spec]` / `#[verifier::exec]` parameter attributes):
/// `#[trust_vc::proof]`, `#[verifier::proof]`, `#[proof]`, and likewise for
/// `spec` / `exec`. `parse_file_allow_tracked` rewrites the Verus `tracked p: T`
/// surface into `#[trust_vc::proof] p: T`, so `tracked` lands here too.
pub(crate) fn explicit_param_mode(attrs: &[syn::Attribute]) -> Option<VarMode> {
    for attr in attrs {
        let segments: Vec<String> = attr
            .path()
            .segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect();
        let name = match segments.as_slice() {
            [prefix, name] if prefix == "trust_vc" || prefix == "verifier" => name.as_str(),
            [name] => name.as_str(),
            _ => continue,
        };
        match name {
            "proof" | "tracked" => return Some(VarMode::Tracked),
            "spec" | "ghost" => return Some(VarMode::Ghost),
            "exec" => return Some(VarMode::Exec),
            _ => {}
        }
    }
    None
}

/// The modes of `sig`'s parameters, given the enclosing function's mode.
fn param_modes(function_mode: FunctionMode, sig: &syn::Signature) -> ParamModes {
    sig.inputs
        .iter()
        .map(|input| match input {
            // `self` receivers carry the function's default parameter mode.
            syn::FnArg::Receiver(receiver) => explicit_param_mode(&receiver.attrs)
                .unwrap_or_else(|| default_param_mode(function_mode)),
            syn::FnArg::Typed(typed) => explicit_param_mode(&typed.attrs)
                .unwrap_or_else(|| default_param_mode(function_mode)),
        })
        .collect()
}

/// The names of `func`'s PROOF-mode parameters (`tracked p` /
/// `#[trust_vc::proof] p`).
fn proof_mode_param_names(func: &syn::ItemFn) -> Vec<String> {
    let function_mode = crate::mode_attrs::classify_item_fn(func);
    let mut names = Vec::new();
    for input in &func.sig.inputs {
        let syn::FnArg::Typed(typed) = input else {
            continue;
        };
        let mode =
            explicit_param_mode(&typed.attrs).unwrap_or_else(|| default_param_mode(function_mode));
        if !matches!(mode, VarMode::Tracked | VarMode::Proof) {
            continue;
        }
        if let syn::Pat::Ident(pat) = typed.pat.as_ref() {
            names.push(pat.ident.to_string());
        }
    }
    names
}

/// Signature catalog: every free / impl / trait fn of the file, by name.
fn catalog_param_modes(file: &syn::File) -> BTreeMap<String, ParamModes> {
    let mut catalog = BTreeMap::new();
    collect_param_modes(&file.items, &mut catalog);
    catalog
}

fn collect_param_modes(items: &[syn::Item], catalog: &mut BTreeMap<String, ParamModes>) {
    for item in items {
        match item {
            syn::Item::Fn(func) => {
                let mode = crate::mode_attrs::classify_item_fn(func);
                catalog
                    .entry(func.sig.ident.to_string())
                    .or_insert_with(|| param_modes(mode, &func.sig));
            }
            syn::Item::Mod(module) => {
                if let Some((_, inner)) = &module.content {
                    collect_param_modes(inner, catalog);
                }
            }
            _ => {}
        }
    }
}

/// Rejects a proof-mode variable CONSUMED (passed to a `tracked` parameter)
/// inside an `assert … by` / `assert forall … by` block, with Verus's verbatim
/// diagnostic.
///
/// Reject-only: returns `Ok(())` unless the enclosing function actually has a
/// proof-mode parameter that a by-block hands to a proof-mode parameter.
pub(crate) fn check_by_block_proof_var_modes(
    file: &syn::File,
    func: &syn::ItemFn,
) -> TrustVcResult<()> {
    let proof_vars = proof_mode_param_names(func);
    if proof_vars.is_empty() {
        return Ok(());
    }
    let catalog = catalog_param_modes(file);
    let mut visitor = ByBlockProofVarVisitor {
        proof_vars: &proof_vars,
        catalog: &catalog,
        violation: None,
    };
    visitor.visit_block(&func.block);
    match visitor.violation {
        Some(expected) => Err(TrustVcError::Encoding {
            context: "extract verification conditions",
            // Verbatim Verus (`vir/src/modes.rs`, `check_expr_has_mode`).
            detail: format!(
                "expression has mode {}, expected mode {expected}",
                VarMode::Ghost
            ),
        }),
        None => Ok(()),
    }
}

struct ByBlockProofVarVisitor<'a> {
    proof_vars: &'a [String],
    catalog: &'a BTreeMap<String, ParamModes>,
    /// The EXPECTED mode of the offending parameter (the observed mode is always
    /// `spec` — the by-block demotion).
    violation: Option<VarMode>,
}

impl ByBlockProofVarVisitor<'_> {
    /// True when `expr` is a bare path naming one of the enclosing function's
    /// proof-mode parameters.
    fn is_proof_var(&self, expr: &syn::Expr) -> bool {
        let syn::Expr::Path(path) = expr else {
            return false;
        };
        path.qself.is_none()
            && path
                .path
                .get_ident()
                .is_some_and(|ident| self.proof_vars.iter().any(|name| ident == name.as_str()))
    }

    /// Walks a by-block body, looking for a call that CONSUMES a proof-mode
    /// variable (passes it to a proof-mode parameter). Inside the block the
    /// variable reads at mode `spec`, so such a call is a mode error.
    fn check_by_block(&mut self, block: &syn::Block) {
        struct CallVisitor<'a, 'b> {
            outer: &'b mut ByBlockProofVarVisitor<'a>,
        }
        impl<'ast> Visit<'ast> for CallVisitor<'_, '_> {
            fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
                if let syn::Expr::Path(path) = call.func.as_ref() {
                    if let Some(ident) = path.path.segments.last() {
                        if let Some(modes) = self.outer.catalog.get(&ident.ident.to_string()) {
                            for (index, arg) in call.args.iter().enumerate() {
                                let Some(param_mode) = modes.get(index) else {
                                    continue;
                                };
                                if !matches!(param_mode, VarMode::Tracked | VarMode::Proof) {
                                    continue;
                                }
                                if self.outer.is_proof_var(arg) && self.outer.violation.is_none() {
                                    self.outer.violation = Some(*param_mode);
                                }
                            }
                        }
                    }
                }
                syn::visit::visit_expr_call(self, call);
            }
        }
        let mut visitor = CallVisitor { outer: self };
        visitor.visit_block(block);
    }
}

impl<'ast> Visit<'ast> for ByBlockProofVarVisitor<'_> {
    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        let name = mac
            .path
            .segments
            .last()
            .map(|segment| segment.ident.to_string())
            .unwrap_or_default();
        match name.as_str() {
            "assert_by" | "trust_vc_assert_by" => {
                if let crate::AssertByParsed::WithProofBlock { proof_block, .. } =
                    crate::parse_assert_by(mac.tokens.clone())
                {
                    if let Ok(block) = syn::parse2::<syn::Block>(proof_block) {
                        self.check_by_block(&block);
                    }
                }
            }
            "assert_forall_by" | "trust_vc_assert_forall_by" => {
                if let Ok(parsed) = crate::parse_assert_forall_by(mac.tokens.clone()) {
                    self.check_by_block(&parsed.proof_block);
                }
            }
            _ => {}
        }
        syn::visit::visit_macro(self, mac);
    }
}
