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
//!    `proof_block!` block) is rejected. Mirrors Verus `ExprX::Assign`:
//!    ```text
//!    if !mode_le(outer_mode, x_mode) {
//!        return Err(error(&expr.span,
//!            format!("cannot assign to {x_mode} variable from {outer_mode} mode")));
//!    }
//!    ```
//!
//! **Rule 2 IS NOT ENFORCED HERE, and deliberately so (2026-09-16).** It was,
//! for one commit, and a token scanner decided it wrong three different ways:
//!
//! * `s.g = 7` — the walker advances one token at a time, so the ident it keys
//!   the assignment on is the LAST one before `=`, i.e. the FIELD `g`. A
//!   `let g` inside the proof block then made the write to the EXEC place
//!   `s.g` look like a write to a proof-local.
//! * `v[0] = 7` — the token before `=` is a bracket `Group`, not an `Ident`, so
//!   no assignment was recognized at all while the engine lowered the write.
//! * `e >>= 3` — the compound table held only the two-character operators, so
//!   the leading `>` of `>>=` was unrecognized.
//!
//! All three are the same defect: **a token scanner is guessing at what PLACE a
//! statement writes.** It cannot see that `s.g` is a field of an exec local,
//! that `v[0]` indexes one, or that `>>=` writes at all — widening the table
//! and special-casing `Group`s would fix those three spellings and leave the
//! class open. The engine already knows: `body_extract` lowers the proof block
//! and resolves the PLACE ROOT of every write with the same
//! `field_index_projection_root` it uses for `&mut` referents. Rule 2 is
//! therefore enforced at the LOWERING SEAM
//! (`vc_extraction::body_extract::check_proof_block_place_writes`), where it is
//! decided by construction and cannot be defeated by a spelling.
//!
//! What stays here is what a token pass can legitimately do: recognizing the
//! block, the mode annotations, the `let`-modifier parsing — and rule 1, which
//! is a statement about a NAME an exec-mode `let` declared, not about a place.
//!
//! The rule-1 diagnostic string is load-bearing for later promotion of upstream
//! `modes.rs` cases, which match it via `assert_vir_error_msg`. It is
//! reproduced byte-for-byte and pinned by tests below.
//!
//! ## Scope of Phase 1
//!
//! The `if spec-condition { ... }` form of rule 2, which requires
//! condition-mode inference, is deferred to a later phase. Initialization of
//! a `ghost`/`tracked` variable in exec (`let ghost b = false;`) is allowed,
//! matching Verus `initialize_{proof,spec}_var_in_exec`.
//!
//! ## Wiring status — WIRED (2026-09-16)
//!
//! Phase 1 landed the lattice ([`crate::mode::VarMode`]), the environment
//! ([`BodyModeEnv`]) and the checker ([`check_body_var_modes`]) deliberately
//! UNWIRED (`88858fc6`, "sound (unwired) substrate"; the companion design doc
//! `docs/archive/design-mutref-mode-wiring.md`, landed at `10ee1071` and later swept out of
//! `docs/` by the export ban at `33d82ea4`, named the wiring as the next
//! increment). It was never disabled and never reverted — it was simply never
//! connected.
//!
//! It is now called from [`crate::vc_extraction`], next to the sibling
//! [`crate::proof_var_mode`] check, for **exec functions only**. Exec-only is
//! not timidity: both rules are statements about an exec-mode body, and the
//! checker's block walk starts in [`BlockMode::Exec`], so running it over a
//! proof/spec function would misclassify that function's (already ghost)
//! locals as exec and over-reject.
//!
//! ### What wiring it closed — a measured FALSE VERIFIED
//!
//! `proof_block!({ ... })` in an exec function is live
//! (`vc_extraction::body_extract::extract_exec_proof_block`) and its
//! assignments propagate into the surrounding solver state. But
//! `trust_vc::proof_block!` expands, in any build without `cfg(trust_mc)`, to
//! `let _ = || { ..body.. };` — a closure that is never called. So before this
//! wiring:
//!
//! ```ignore
//! let mut e: u64 = 0;
//! trust_vc::proof_block!({ e = 7; });
//! trust_vc::assert!(e == 7u64);   // Verified
//! ```
//!
//! verified, while at RUNTIME `e` is still `0` — the verifier believed a
//! mutation the compiler erases. The liar twin `assert!(e == 0u64)` came back
//! `Counterexample`, so the solver genuinely held `e == 7`. That is exactly
//! the program upstream Verus rejects with rule 2 below, and rejecting it is
//! what the rule is for. Pinned in
//! `crates/trust-vc-core/src/vc_extraction/tests/proof_block_ghost_add.rs`.

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

    // Native surface: `proof_block!({ ... })` / `trust_vc::proof_block!({ ... })`
    // is trust-vc's spelling of Verus's `proof { ... }`. Recurse in proof mode.
    if let Some((inner, after)) = proof_block_macro(tokens, idx) {
        check_block(&inner, BlockMode::Proof, env)?;
        return Ok((LeadingStmt::Other, skip_optional_semicolon(tokens, after)));
    }

    // Native surface: `#[trust_vc::spec] let ...` / `#[trust_vc::proof] let ...`,
    // the attribute form that `tracked_syntax::normalize_ghost_tracked_local_tokens`
    // rewrites `let ghost` / `let tracked` into.
    if let Some((attr_mode, let_idx)) = leading_mode_attribute(tokens, idx) {
        if is_ident(tokens.get(let_idx), "let") {
            let (_, name_idx) = parse_let_modifiers(tokens, let_idx + 1, mode);
            if let Some(TokenTree::Ident(name)) = tokens.get(name_idx) {
                env.declare(name.to_string(), attr_mode);
            }
            let after = skip_to_statement_end(tokens, name_idx);
            return Ok((LeadingStmt::Decl, after));
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
        if assignment_operator_at(tokens, idx + 1) {
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

/// Recognizes `proof_block!( { .. } )` / `trust_vc::proof_block!( { .. } )` at
/// `idx`, returning the block's inner tokens and the index just past the macro
/// call (before any trailing `;`).
///
/// Only the STATEMENT-position spelling is recognized. A `proof_block!` used as
/// a value expression is rejected outright by
/// `body_extract::extract_exec_proof_block`, so it never reaches a verdict.
fn proof_block_macro(tokens: &[TokenTree], idx: usize) -> Option<(Vec<TokenTree>, usize)> {
    // Optional `trust_vc ::` (or any single-segment) path qualifier.
    let name_idx = if matches!(tokens.get(idx), Some(TokenTree::Ident(_)))
        && is_punct(tokens.get(idx + 1), ':')
        && is_punct(tokens.get(idx + 2), ':')
        && matches!(tokens.get(idx + 3), Some(TokenTree::Ident(_)))
    {
        idx + 3
    } else {
        idx
    };
    // `body_extract` dispatches BOTH spellings (`"proof_block" |
    // "trust_vc_proof_block"`), and `macro_scope::SPEC_MACRO_NAMES` carries a
    // `trust_vc_`-prefixed alias for every spec macro. Matching only the bare
    // ident left the alias walking straight past this pass.
    if !is_ident(tokens.get(name_idx), "proof_block")
        && !is_ident(tokens.get(name_idx), "trust_vc_proof_block")
    {
        return None;
    }
    if !is_punct(tokens.get(name_idx + 1), '!') {
        return None;
    }
    let TokenTree::Group(args) = tokens.get(name_idx + 2)? else {
        return None;
    };
    // `proof_block!({ .. })`, `proof_block![{ .. }]` or `proof_block!{ .. }`.
    let inner: Vec<TokenTree> = match args.delimiter() {
        Delimiter::Brace => args.stream().into_iter().collect(),
        _ => match args.stream().into_iter().next() {
            Some(TokenTree::Group(block)) if block.delimiter() == Delimiter::Brace => {
                block.stream().into_iter().collect()
            }
            _ => args.stream().into_iter().collect(),
        },
    };
    Some((inner, name_idx + 3))
}

/// Reads a leading `#[trust_vc::spec]` / `#[trust_vc::proof]` (or the
/// `verifier::` / bare spellings) attribute at `idx`, returning the [`VarMode`]
/// it declares and the index just past the attribute.
///
/// Mirrors `proof_var_mode::explicit_param_mode`, which reads the same markers
/// off a PARAMETER; here they sit on a `let`.
fn leading_mode_attribute(tokens: &[TokenTree], idx: usize) -> Option<(VarMode, usize)> {
    if !is_punct(tokens.get(idx), '#') {
        return None;
    }
    let TokenTree::Group(group) = tokens.get(idx + 1)? else {
        return None;
    };
    if group.delimiter() != Delimiter::Bracket {
        return None;
    }
    let segments: Vec<TokenTree> = group.stream().into_iter().collect();
    // Last ident in the attribute path is the mode name.
    let last = segments.iter().rev().find_map(|token| match token {
        TokenTree::Ident(ident) => Some(ident.to_string()),
        _ => None,
    })?;
    let mode = match last.as_str() {
        "proof" | "tracked" => VarMode::Tracked,
        "spec" | "ghost" => VarMode::Ghost,
        "exec" => VarMode::Exec,
        _ => return None,
    };
    Some((mode, idx + 2))
}

fn is_punct(token: Option<&TokenTree>, ch: char) -> bool {
    matches!(token, Some(TokenTree::Punct(punct)) if punct.as_char() == ch)
}

/// Enforces RULE 1 for an assignment to bare local `name`.
///
/// Rule 2 (`cannot assign to exec variable from proof mode`) is deliberately
/// NOT here — see the module header. Deciding it needs the PLACE a statement
/// writes and the ROOT local of that place, which a token pass cannot compute;
/// it is enforced at the lowering seam instead
/// (`vc_extraction::body_extract::check_proof_block_place_writes`).
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

/// Whether an assignment operator starts at `tokens[idx]`: a bare `=`, a
/// two-character compound `op=` (`+=`, `&=`, ...), or a three-character shift
/// compound (`<<=`, `>>=`).
///
/// **The `=` must actually be there.** An earlier revision accepted ANY Joint
/// punct whose character was in the compound table, without looking at what it
/// was joined TO. The first `&` of `&&` and the first `|` of `||` are Joint, so
/// `flag && cond` read as an assignment to `flag` — and since an unmodelled
/// name defaults to exec, every honest `&&` / `||` inside a proof block was
/// REJECTED. That over-rejection is what this predicate's next-token
/// requirement exists to prevent; `&&`, `||`, `<<`, `>>`, `==`, `!=`, `<=`,
/// `>=`, `->` and `=>` are all excluded by it.
fn assignment_operator_at(tokens: &[TokenTree], idx: usize) -> bool {
    let Some(TokenTree::Punct(punct)) = tokens.get(idx) else {
        return false;
    };
    let joint = matches!(punct.spacing(), proc_macro2::Spacing::Joint);
    match punct.as_char() {
        // A bare `=` is Alone; the leading `=` of `==` is Joint.
        '=' => !joint,
        // `op=`: the operator char is Joint and the NEXT punct must be `=`.
        '+' | '-' | '*' | '/' | '%' | '&' | '|' | '^' => {
            joint && is_punct(tokens.get(idx + 1), '=')
        }
        // `<<=` / `>>=`: two joined shift chars, then `=`.
        ch @ ('<' | '>') => {
            joint
                && matches!(tokens.get(idx + 1), Some(TokenTree::Punct(second))
                    if second.as_char() == ch
                        && matches!(second.spacing(), proc_macro2::Spacing::Joint))
                && is_punct(tokens.get(idx + 2), '=')
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

    // --- Rule 2 is NOT this module's job (2026-09-16) ---

    /// Rule 2 moved to the LOWERING SEAM. This pass must stay SILENT about a
    /// proof-mode write to an exec place — not because such a write is legal
    /// (it is a false `Verified`; `body_extract::check_proof_block_place_writes`
    /// rejects it), but because a second, token-level opinion here diverged
    /// from the seam's in three measured ways and over-rejected in a fourth.
    #[test]
    fn rule_two_is_not_enforced_by_the_token_pass() {
        for body in [
            quote! { let mut e = false; proof { e = true; } },
            quote! { let mut e = 0u64; trust_vc::proof_block!({ e = 7u64; }); },
        ] {
            assert!(
                check(body).is_ok(),
                "rule 2 belongs to the lowering seam; the token pass must not \
                 duplicate it"
            );
        }
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
        // STATEMENT position: a `let` is routed through `skip_to_statement_end`
        // and never reaches `assignment_operator_at`, so a `let`-shaped body
        // pins nothing about the predicate.
        for body in [
            quote! { let ghost b; b >= false; },
            quote! { let ghost b; b <= false; },
            quote! { let ghost b; b != false; },
            quote! { let ghost b; b == false; },
            quote! { let ghost a = 1; a -> 2; },
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

    // --- Native surface: `proof_block!` and the attribute mode form ---

    /// A `proof_block!` must SUPPRESS rule 1 for its contents: inside it, a
    /// ghost/tracked local is legally assignable. All the spellings the engine
    /// dispatches — including the `trust_vc_proof_block` ALIAS that
    /// `body_extract` matches next to the bare name and that
    /// `macro_scope::SPEC_MACRO_NAMES` carries for every spec macro — must be
    /// recognized, or a ghost assignment inside the block reads as an exec-mode
    /// mutation of a ghost var and is wrongly rejected.
    #[test]
    fn proof_block_spellings_suppress_rule_one() {
        for body in [
            quote! { #[trust_vc::spec] let mut j = 0u64; trust_vc::proof_block!({ j = 2u64; }); },
            quote! { #[trust_vc::spec] let mut j = 0u64; proof_block!({ j = 2u64; }); },
            quote! { #[trust_vc::spec] let mut j = 0u64; proof_block!{{ j = 2u64; }} },
            quote! { #[trust_vc::spec] let mut j = 0u64; trust_vc::trust_vc_proof_block!({ j = 2u64; }); },
            quote! { #[trust_vc::spec] let mut j = 0u64; trust_vc_proof_block!({ j = 2u64; }); },
        ] {
            assert!(
                check(body).is_ok(),
                "every dispatched proof_block spelling must enter proof mode"
            );
        }
    }

    /// The ALIAS control: without the `trust_vc_proof_block` arm this body is
    /// read as exec-mode and rule 1 fires on the ghost assignment.
    #[test]
    fn alias_spelling_is_recognized_as_a_proof_block() {
        let tokens: Vec<TokenTree> = quote!(trust_vc_proof_block!({
            x = 1;
        }))
        .into_iter()
        .collect();
        assert!(
            super::proof_block_macro(&tokens, 0).is_some(),
            "the alias the engine itself dispatches must be recognized here"
        );
    }

    #[test]
    fn attribute_form_mode_markers_declare_binding_modes() {
        // `normalize_ghost_tracked_local_tokens` rewrites `let ghost x` into
        // `#[trust_vc::spec] let x`; the checker must read the mode back off
        // the attribute.
        for body in [
            quote! { #[trust_vc::spec] let b = false; b = true; },
            quote! { #[trust_vc::proof] let b = false; b = true; },
            quote! { #[verifier::spec] let b = false; b = true; },
        ] {
            assert!(
                err_message(body).contains("exec code cannot mutate non-exec variable"),
                "an attribute-declared ghost/tracked local must obey rule 1"
            );
        }
    }

    #[test]
    fn exec_attribute_and_unknown_attributes_stay_exec() {
        // `#[trust_vc::exec]` is exec; an unrelated attribute must not be read
        // as a mode marker (that would over-reject an ordinary local).
        for body in [
            quote! { #[trust_vc::exec] let mut b = 0u64; b = 1u64; },
            quote! { #[allow(unused)] let mut b = 0u64; b = 1u64; },
            quote! { #[cfg(test)] let mut b = 0u64; b = 1u64; },
        ] {
            assert!(check(body).is_ok());
        }
    }

    // --- Finding 5: `&&` / `||` must never read as an assignment ---

    /// MEASURED OVER-REJECTION. The first `&` of `&&` and the first `|` of
    /// `||` are `Spacing::Joint`, and the predicate accepted any Joint punct in
    /// the compound table without checking what it was joined TO. So
    /// `if flag && cond` read as an assignment to `flag`, and since an
    /// unmodelled name defaults to exec, every honest `&&` / `||` inside a
    /// proof block was rejected. The pattern is everywhere.
    ///
    /// NON-VACUITY, and this test was vacuous once: every body below is in
    /// STATEMENT position (`flag && true;`), NOT `let _ = flag && true;`. A
    /// `let` statement is classified by `classify_statement`'s `let` arm, which
    /// calls `skip_to_statement_end` — the `&&` never reaches the assignment
    /// predicate at all, so the earlier `let`-shaped bodies passed under the
    /// BROKEN predicate too and pinned nothing. A bare leading ident is the only
    /// shape that reaches `assignment_operator_at`.
    ///
    /// Reverting `assignment_operator_at`'s next-token requirement to the
    /// joint-only predicate makes every row here fail with rule 1's
    /// `exec code cannot mutate non-exec variable`.
    #[test]
    fn logical_and_or_are_not_assignments() {
        for body in [
            quote! { let ghost flag = true; flag && true; },
            quote! { let ghost flag = true; flag || true; },
            quote! { let ghost flag = true; flag & true; },
            quote! { let ghost flag = true; flag | true; },
            quote! { let ghost a = 1; a << 2; },
            quote! { let ghost a = 1; a >> 2; },
            quote! { let ghost a = 1; a + 2; },
            quote! { let ghost a = 1; a - 2; },
            quote! { let ghost a = 1; a * 2; },
            quote! { let ghost a = 1; a / 2; },
            quote! { let ghost a = 1; a % 2; },
            quote! { let ghost a = 1; a ^ 2; },
            quote! { let ghost flag = true; if flag && true { } },
            quote! { let ghost flag = true; if flag || true { } },
        ] {
            let rendered = body.to_string();
            assert!(
                check(body).is_ok(),
                "a Joint punct is an assignment operator only when the NEXT \
                 punct is `=` — `{rendered}` contains no write"
            );
        }
    }

    /// The non-vacuity twin: the genuine compound assignments, INCLUDING the
    /// three-character shifts the old two-character table missed, must still be
    /// recognized as writes.
    #[test]
    fn compound_assignments_including_shifts_are_recognized() {
        for body in [
            quote! { let ghost mut a = 1; a += 1; },
            quote! { let ghost mut a = 1; a &= 1; },
            quote! { let ghost mut a = 1; a |= 1; },
            quote! { let ghost mut a = 1; a ^= 1; },
            quote! { let ghost mut a = 1; a <<= 1; },
            quote! { let ghost mut a = 1; a >>= 1; },
        ] {
            assert!(
                err_message(body).contains("exec code cannot mutate non-exec variable"),
                "a genuine compound assignment must still be seen as a write"
            );
        }
    }

    #[test]
    fn is_ident_recognizes_named_ident() {
        let tokens: Vec<TokenTree> = quote!(proof).into_iter().collect();
        assert!(super::is_ident(tokens.first(), "proof"));
        assert!(!super::is_ident(tokens.first(), "exec"));
    }
}
