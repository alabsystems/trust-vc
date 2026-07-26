//! Body-level variable-mode tracking (backlog #3, Phase 1).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Grows the function-level mode model ([`crate::mode`]) into a per-body,
//! per-binding view. Verus assigns every `let` binding inside a body a
//! [`VarMode`] and enforces the *assign/declare-in-exec* rules (Verus's
//! `modes.rs`, rule cluster **R3**). This module is the smallest sound slice
//! of that pass: it tracks `let ghost` / `let tracked` / plain `let`
//! declarations and `proof { ... }` blocks, then checks assignments against
//! the binding modes.
//!
//! ## The two rules (and their verbatim Verus diagnostics)
//!
//! 1. **exec code cannot mutate non-exec variable** — in an exec-mode block,
//!    an assignment whose left-hand side is a non-exec (`ghost`/`tracked`)
//!    variable is rejected. Mirrors Verus
//!    `source/vir/src/modes.rs` `get_var_loc_mode`:
//!    ```text
//!    if ctxt.check_ghost_blocks
//!        && typing.block_ghostness == Ghost::Exec
//!        && x_mode != Mode::Exec
//!    { return Err(error(&expr.span, "exec code cannot mutate non-exec variable")); }
//!    ```
//!
//! 2. **cannot assign to exec variable from proof mode** — assigning to an
//!    exec variable while the surrounding mode is proof (e.g. inside a
//!    `proof { ... }` block) is rejected. Mirrors Verus `ExprX::Assign`:
//!    ```text
//!    if !mode_le(outer_mode, x_mode) {
//!        return Err(error(&expr.span,
//!            format!("cannot assign to {x_mode} variable from {outer_mode} mode")));
//!    }
//!    ```
//!    The message is templated; for an exec variable assigned from proof mode
//!    it reads exactly `cannot assign to exec variable from proof mode`.
//!
//! Both diagnostic strings are load-bearing for later promotion of upstream
//! `modes.rs` cases, which match them via `assert_vir_error_msg`. They are
//! reproduced byte-for-byte and pinned by tests below.
//!
//! ## Scope of Phase 1
//!
//! This slice models the `proof { ... }`-block form of rule 2 (outer mode
//! becomes proof). The `if spec-condition { ... }` form, which requires
//! condition-mode inference, is deferred to a later phase. Initialization of
//! a `ghost`/`tracked` variable in exec (`let ghost b = false;`) is allowed,
//! matching Verus `initialize_{proof,spec}_var_in_exec`.
//!
//! ## Wiring status
//!
//! Phase 1 lands the lattice ([`crate::mode::VarMode`]), the environment
//! ([`BodyModeEnv`]), and the checker ([`check_body_var_modes`]) with full
//! unit-test coverage. Invoking the checker from `proof_expand.rs` /
//! `spec_expand.rs` / exec-fn expansion (so it gates live verification and
//! promotes the upstream `modes.rs` cases) is the next phase; until then the
//! production entry points are exercised only by this module's tests, hence
//! the module-level `dead_code` allowance.
#![allow(dead_code)]

use crate::error::{TrustVcError, TrustVcResult};
use crate::mode::VarMode;
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use std::collections::HashMap;

/// Verbatim Verus diagnostic for mutating a ghost/tracked variable from an
/// exec-mode block.
pub(crate) const EXEC_MUTATE_NON_EXEC: &str = "exec code cannot mutate non-exec variable";

/// The block ghostness of the statement being checked: either ordinary exec
/// code, or a `proof { ... }` (ghost) block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BlockMode {
    /// Ordinary executable code.
    Exec,
    /// Inside a `proof { ... }` block.
    Proof,
}

impl BlockMode {
    /// The outer [`VarMode`] an assignment is checked against in this block.
    fn outer_var_mode(self) -> VarMode {
        match self {
            BlockMode::Exec => VarMode::Exec,
            BlockMode::Proof => VarMode::Proof,
        }
    }
}

/// `Γ`: the body-level mapping from binding name to its [`VarMode`].
///
/// A scope stack lets `proof { ... }` blocks and nested braces shadow and then
/// drop bindings. Lookups walk from the innermost scope outward, so an inner
/// binding shadows an outer one with the same name.
#[derive(Debug, Default)]
pub(crate) struct BodyModeEnv {
    scopes: Vec<HashMap<String, VarMode>>,
}

impl BodyModeEnv {
    /// Creates an environment with a single (outermost) scope.
    pub(crate) fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
        }
    }

    /// Enters a nested scope.
    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Leaves the innermost scope. The outermost scope is never popped.
    fn pop_scope(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    /// Records the mode of a binding in the innermost scope.
    fn declare(&mut self, name: impl Into<String>, mode: VarMode) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.into(), mode);
        }
    }

    /// Looks up a binding's mode, searching innermost-to-outermost.
    ///
    /// Returns `None` for unknown names (e.g. function parameters, which this
    /// Phase-1 slice does not model). Unknown names are treated as exec by the
    /// checker, which keeps the slice sound: it only ever *adds* the R3
    /// rejections it can prove, never relaxes anything.
    pub(crate) fn mode_of(&self, name: &str) -> Option<VarMode> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }
}

/// Checks the variable-mode (R3) rules over a function body given as a token
/// stream (the body's `{ ... }` contents, without the outer braces).
///
/// Returns `Ok(())` if no R3 violation is found, or a [`TrustVcError`] whose
/// message is the verbatim Verus diagnostic for the first violation.
///
/// The body starts in exec mode; a `proof { ... }` statement enters proof
/// mode for its contents.
pub(crate) fn check_body_var_modes(body: TokenStream) -> TrustVcResult<()> {
    let mut env = BodyModeEnv::new();
    check_block(
        &body.into_iter().collect::<Vec<_>>(),
        BlockMode::Exec,
        &mut env,
    )
}

/// The assignment outcome for a single statement-leading identifier.
enum LeadingStmt {
    /// A `let` declaration: `(name, mode)` was declared.
    Decl,
    /// An assignment `name = ...` / `name op= ...` to `name`.
    Assign(String),
    /// Anything else (a call, expression, control flow, …) we do not model.
    Other,
}

/// Walks the statements of one brace-delimited block in `mode`.
fn check_block(tokens: &[TokenTree], mode: BlockMode, env: &mut BodyModeEnv) -> TrustVcResult<()> {
    env.push_scope();
    let result = check_statements(tokens, mode, env);
    env.pop_scope();
    result
}

#[allow(clippy::indexing_slicing)] // index advance is bounded by `idx < tokens.len()`
fn check_statements(
    tokens: &[TokenTree],
    mode: BlockMode,
    env: &mut BodyModeEnv,
) -> TrustVcResult<()> {
    let mut idx = 0;
    while idx < tokens.len() {
        match classify_statement(tokens, idx, mode, env)? {
            (LeadingStmt::Decl, next) | (LeadingStmt::Other, next) => idx = next,
            (LeadingStmt::Assign(name), next) => {
                check_assignment(&name, mode, env, &tokens[idx])?;
                idx = next;
            }
        }
    }
    Ok(())
}

/// Classifies the statement that begins at `tokens[idx]`, advancing the body's
/// declaration environment for `let` statements and recursing into
/// `proof { ... }` and other brace groups. Returns the classification plus the
/// index just past the statement.
#[allow(clippy::indexing_slicing)] // all indexing is guarded by `< tokens.len()` checks
fn classify_statement(
    tokens: &[TokenTree],
    idx: usize,
    mode: BlockMode,
    env: &mut BodyModeEnv,
) -> TrustVcResult<(LeadingStmt, usize)> {
    // `proof { ... }` block: recurse in proof mode.
    if is_ident(Some(&tokens[idx]), "proof") {
        if let Some(TokenTree::Group(group)) = tokens.get(idx + 1) {
            if group.delimiter() == Delimiter::Brace {
                let inner: Vec<TokenTree> = group.stream().into_iter().collect();
                check_block(&inner, BlockMode::Proof, env)?;
                let after = skip_optional_semicolon(tokens, idx + 2);
                return Ok((LeadingStmt::Other, after));
            }
        }
    }

    // `let [ghost|tracked] [mut] NAME ...;`
    if is_ident(Some(&tokens[idx]), "let") {
        let (var_mode, name_idx) = parse_let_modifiers(tokens, idx + 1, mode);
        if let Some(TokenTree::Ident(name)) = tokens.get(name_idx) {
            env.declare(name.to_string(), var_mode);
        }
        let after = skip_to_statement_end(tokens, name_idx);
        return Ok((LeadingStmt::Decl, after));
    }

    // `NAME = ...;` or `NAME op= ...;` — a place assignment to a bare local.
    if let TokenTree::Ident(name) = &tokens[idx] {
        if is_assignment_operator(tokens.get(idx + 1)) {
            let after = skip_to_statement_end(tokens, idx + 1);
            return Ok((LeadingStmt::Assign(name.to_string()), after));
        }
    }

    // Any other token: descend into brace groups (blocks, control-flow bodies)
    // keeping the current mode, otherwise just advance one token.
    if let TokenTree::Group(group) = &tokens[idx] {
        if group.delimiter() == Delimiter::Brace {
            let inner: Vec<TokenTree> = group.stream().into_iter().collect();
            check_block(&inner, mode, env)?;
        }
    }
    Ok((LeadingStmt::Other, idx + 1))
}

/// Enforces the R3 rules for an assignment to bare local `name`.
fn check_assignment(
    name: &str,
    mode: BlockMode,
    env: &BodyModeEnv,
    lhs_token: &TokenTree,
) -> TrustVcResult<()> {
    // Unknown names (params, fields, etc.) are conservatively exec; this slice
    // only models bare locals it has seen declared.
    let x_mode = env.mode_of(name).unwrap_or(VarMode::Exec);

    // Rule 1: exec code cannot mutate a non-exec (ghost/tracked) variable.
    if mode == BlockMode::Exec && !x_mode.is_exec() {
        return Err(mode_error(lhs_token, EXEC_MUTATE_NON_EXEC.to_string()));
    }

    // Rule 2: cannot assign to a lower-mode variable from a higher outer mode,
    // e.g. assigning to an exec variable from inside a `proof { ... }` block.
    let outer_mode = mode.outer_var_mode();
    if !outer_mode.le(x_mode) {
        return Err(mode_error(
            lhs_token,
            format!(
                "cannot assign to {} variable from {} mode",
                x_mode, outer_mode
            ),
        ));
    }

    Ok(())
}

/// Parses an optional `ghost` / `tracked` modifier and an optional `mut`
/// after `let`, returning the binding's [`VarMode`] and the index of the
/// binding name. `mode` is the current block mode (a plain `let` in a proof
/// block is a proof/tracked-context binding, matching Verus).
fn parse_let_modifiers(tokens: &[TokenTree], start: usize, mode: BlockMode) -> (VarMode, usize) {
    let mut idx = start;
    let mut var_mode = match mode {
        BlockMode::Exec => VarMode::Exec,
        BlockMode::Proof => VarMode::Tracked,
    };

    if is_ident(tokens.get(idx), "ghost") {
        var_mode = VarMode::Ghost;
        idx += 1;
    } else if is_ident(tokens.get(idx), "tracked") {
        var_mode = VarMode::Tracked;
        idx += 1;
    }

    if is_ident(tokens.get(idx), "mut") {
        idx += 1;
    }

    (var_mode, idx)
}

/// Advances past the next top-level `;`, returning the index after it. If no
/// semicolon is found before the end of the slice, returns `tokens.len()`.
fn skip_to_statement_end(tokens: &[TokenTree], start: usize) -> usize {
    let mut idx = start;
    while idx < tokens.len() {
        if is_semicolon(tokens.get(idx)) {
            return idx + 1;
        }
        idx += 1;
    }
    tokens.len()
}

/// Skips a single optional trailing `;` at `idx`.
fn skip_optional_semicolon(tokens: &[TokenTree], idx: usize) -> usize {
    if is_semicolon(tokens.get(idx)) {
        idx + 1
    } else {
        idx
    }
}

/// Whether `token` is an assignment operator: bare `=`, or a compound `op=`
/// (e.g. `+=`). A `==` comparison is *not* an assignment.
fn is_assignment_operator(token: Option<&TokenTree>) -> bool {
    match token {
        Some(TokenTree::Punct(punct)) if punct.as_char() == '=' => {
            // A bare `=` has Spacing::Alone; `==`/`+=`-style joints are Joint.
            // We only treat the leading `=` as assignment; for compound `op=`
            // the operator char precedes `=`, handled below.
            matches!(punct.spacing(), proc_macro2::Spacing::Alone)
        }
        Some(TokenTree::Punct(punct)) => {
            // Compound assignment leading punct (e.g. `+` in `+=`) is Joint and
            // the next token would be `=`. Treat common arithmetic/bitwise
            // compound operators as assignment leads only when joined to `=`.
            matches!(punct.spacing(), proc_macro2::Spacing::Joint)
                && matches!(
                    punct.as_char(),
                    '+' | '-' | '*' | '/' | '%' | '&' | '|' | '^'
                )
        }
        _ => false,
    }
}

fn mode_error(token: &TokenTree, detail: String) -> TrustVcError {
    let _ = token; // span reserved for future diagnostic enrichment
    TrustVcError::Encoding {
        context: "variable-mode check",
        detail,
    }
}

fn is_ident(token: Option<&TokenTree>, name: &str) -> bool {
    matches!(token, Some(TokenTree::Ident(ident)) if ident == name)
}

fn is_semicolon(token: Option<&TokenTree>) -> bool {
    matches!(token, Some(TokenTree::Punct(punct)) if punct.as_char() == ';')
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    fn check(body: TokenStream) -> TrustVcResult<()> {
        check_body_var_modes(body)
    }

    fn err_message(body: TokenStream) -> String {
        check(body)
            .expect_err("body should be rejected by the variable-mode checker")
            .to_string()
    }

    // --- Verbatim diagnostic-string pins (load-bearing for promotion) ---

    #[test]
    fn diagnostic_strings_match_verus_verbatim() {
        assert_eq!(
            super::EXEC_MUTATE_NON_EXEC,
            "exec code cannot mutate non-exec variable"
        );
    }

    // --- Rule 1: exec code cannot mutate non-exec variable ---

    #[test]
    fn assign_tracked_var_in_exec_is_rejected() {
        // Verus: assign_proof_var_in_exec
        let body = quote! {
            let tracked b;
            b = false;
        };
        assert!(
            err_message(body).contains("exec code cannot mutate non-exec variable"),
            "assigning a tracked var in exec must hit the R3 mutate diagnostic"
        );
    }

    #[test]
    fn assign_ghost_var_in_exec_is_rejected() {
        // Verus: assign_spec_var_in_exec
        let body = quote! {
            let ghost b;
            b = false;
        };
        assert!(err_message(body).contains("exec code cannot mutate non-exec variable"));
    }

    #[test]
    fn compound_assign_to_ghost_var_in_exec_is_rejected() {
        let body = quote! {
            let ghost mut b;
            b += 1;
        };
        assert!(err_message(body).contains("exec code cannot mutate non-exec variable"));
    }

    // --- Rule 2: cannot assign to exec variable from proof mode ---

    #[test]
    fn assign_exec_var_from_proof_block_is_rejected() {
        // Verus: ghost_wrapper_assign_fail3
        let body = quote! {
            let mut e = false;
            proof {
                e = true;
            }
        };
        assert_eq!(
            err_message(body),
            "variable-mode check: cannot assign to exec variable from proof mode"
        );
    }

    #[test]
    fn assign_exec_var_from_proof_block_message_is_verbatim() {
        let body = quote! {
            let mut e = false;
            proof { e = true; }
        };
        assert!(
            err_message(body).contains("cannot assign to exec variable from proof mode"),
            "rule-2 message must reproduce the Verus diagnostic verbatim"
        );
    }

    // --- Accepted cases (must NOT regress to errors) ---

    #[test]
    fn initialize_tracked_var_in_exec_is_accepted() {
        // Verus: initialize_proof_var_in_exec
        let body = quote! {
            let tracked b = false;
        };
        assert!(
            check(body).is_ok(),
            "initializing a tracked var in exec is legal"
        );
    }

    #[test]
    fn initialize_ghost_var_in_exec_is_accepted() {
        // Verus: initialize_spec_var_in_exec
        let body = quote! {
            let ghost b = false;
        };
        assert!(check(body).is_ok());
    }

    #[test]
    fn declare_tracked_var_then_assign_in_proof_is_accepted() {
        // Verus: declare_proof_var_in_exec
        let body = quote! {
            let tracked b;
            proof {
                b = false;
            }
        };
        assert!(
            check(body).is_ok(),
            "a tracked var declared in exec may be assigned inside a proof block"
        );
    }

    #[test]
    fn declare_ghost_var_then_assign_in_proof_is_accepted() {
        // Verus: declare_spec_var_in_exec
        let body = quote! {
            let ghost mut b;
            proof {
                b = false;
            }
        };
        assert!(check(body).is_ok());
    }

    #[test]
    fn plain_exec_assignment_is_accepted() {
        let body = quote! {
            let mut a = 2;
            a = a + 1;
        };
        assert!(check(body).is_ok());
    }

    #[test]
    fn assign_tracked_var_inside_proof_is_accepted() {
        // proof-mode assignment to a tracked (proof) variable: legal.
        let body = quote! {
            let tracked b;
            proof {
                b = false;
            }
        };
        assert!(check(body).is_ok());
    }

    #[test]
    fn equality_comparison_is_not_an_assignment() {
        // `==` must not be mistaken for an assignment to a ghost var.
        let body = quote! {
            let ghost b;
            let _ok = b == false;
        };
        assert!(
            check(body).is_ok(),
            "`==` is a comparison, not an assignment, and must not trip R3"
        );
    }

    #[test]
    fn empty_body_is_accepted() {
        assert!(check(quote! {}).is_ok());
    }

    #[test]
    fn relational_operators_are_not_assignments() {
        // `>=`, `<=`, `!=` must not be misread as compound assignments to a
        // ghost variable.
        for body in [
            quote! { let ghost b; let _ = b >= false; },
            quote! { let ghost b; let _ = b <= false; },
            quote! { let ghost b; let _ = b != false; },
        ] {
            assert!(
                check(body).is_ok(),
                "relational operators must not be treated as ghost-var assignments"
            );
        }
    }

    #[test]
    fn proof_block_assigning_tracked_var_declared_inside_is_accepted() {
        // A tracked var declared *inside* the proof block, assigned there.
        let body = quote! {
            proof {
                let tracked t;
                t = false;
            }
        };
        assert!(check(body).is_ok());
    }

    #[test]
    fn shadowing_does_not_leak_proof_var_mode_into_exec() {
        // After a proof block ends, an exec local with the same name is exec.
        let body = quote! {
            proof {
                let tracked b;
                b = false;
            }
            let mut b = 0;
            b = 1;
        };
        assert!(
            check(body).is_ok(),
            "the exec `b` after the proof block is exec-mode and freely assignable"
        );
    }

    // --- BodyModeEnv scoping ---

    #[test]
    fn env_declares_and_looks_up_modes() {
        let mut env = BodyModeEnv::new();
        env.declare("g", VarMode::Ghost);
        env.declare("t", VarMode::Tracked);
        env.declare("e", VarMode::Exec);
        assert_eq!(env.mode_of("g"), Some(VarMode::Ghost));
        assert_eq!(env.mode_of("t"), Some(VarMode::Tracked));
        assert_eq!(env.mode_of("e"), Some(VarMode::Exec));
        assert_eq!(env.mode_of("unknown"), None);
    }

    #[test]
    fn inner_scope_shadows_outer_then_restores() {
        let mut env = BodyModeEnv::new();
        env.declare("x", VarMode::Exec);
        env.push_scope();
        env.declare("x", VarMode::Ghost);
        assert_eq!(env.mode_of("x"), Some(VarMode::Ghost));
        env.pop_scope();
        assert_eq!(env.mode_of("x"), Some(VarMode::Exec));
    }

    #[test]
    fn is_ident_recognizes_named_ident() {
        let tokens: Vec<TokenTree> = quote!(proof).into_iter().collect();
        assert!(super::is_ident(tokens.first(), "proof"));
        assert!(!super::is_ident(tokens.first(), "exec"));
    }
}
