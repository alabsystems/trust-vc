//! TrustVc proc macros — 59 Verus-style verification attributes and function macros.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This is the proof-language surface of trust-vc, the proof backend of Trust
//! (the rustc fork). Drop-in Verus parity for these attributes is the
//! benchmark/gate; the destination is Trust's proof calculus on the pure-Rust
//! `ay` solver. See `design-trust-proof-backend.md`.
//!
//! Each entrypoint delegates to a submodule; see per-macro `///` docs below.

mod attr_entrypoints;
mod bridge_entrypoints;
#[path = "closure_expand/mod.rs"]
mod closure_expand;
mod condition_idents;
mod contract_expand;
mod decreases_to_parser;
#[cfg(test)]
mod driver_surface_bridge_tests;
mod loop_infer;
mod macro_expand;
mod macro_expand_ext;
mod macro_expand_ext_loops;
mod old_rewriter;
mod postcondition_lowering;
mod proof_entrypoints;
mod solver_entrypoints;

use proc_macro::TokenStream;

/// Marks a function as a proof function (verified but erased at runtime).
#[proc_macro_attribute]
pub fn proof(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::proof(attr, item)
}

/// Specifies a termination measure (lexicographic, `when`/`via` clauses).
#[proc_macro_attribute]
pub fn decreases(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::decreases(attr, item)
}

/// Marks a lemma for automatic broadcast with trigger-based instantiation.
#[proc_macro_attribute]
pub fn broadcast(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::broadcast(attr, item)
}

/// Assigns a broadcast lemma to a named import group.
#[proc_macro_attribute]
pub fn broadcast_group(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::broadcast_group(attr, item)
}

/// Specifies SMT trigger patterns for quantified formulas.
///
/// Supports `#[trust_vc::trigger(pattern)]`, legacy `#[trust_vc::trigger(group, pattern)]`,
/// and named-group `#[trust_vc::trigger(pattern, group = n)]`.
#[proc_macro_attribute]
pub fn trigger(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::trigger(attr, item)
}

/// Conservative automatic trigger inference for quantified lemmas.
#[proc_macro_attribute]
pub fn auto_trigger(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::auto_trigger(attr, item)
}

/// Aggressive automatic trigger inference for quantified lemmas.
#[proc_macro_attribute]
pub fn all_triggers(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::all_triggers(attr, item)
}

/// Marks a function as a specification function (ghost code for verification).
#[proc_macro_attribute]
pub fn spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::spec(attr, item)
}

/// Marks a trait declaration as verification-relevant surface metadata.
#[proc_macro_attribute]
pub fn trait_spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::trait_spec(attr, item)
}

/// Marks a trait impl block as verification-relevant implementation metadata.
#[proc_macro_attribute]
pub fn trait_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::trait_impl(attr, item)
}

/// Registers a function as Spec mode without modifying its body.
///
/// Use for test helper functions that are semantically pure (spec) but need
/// to remain callable at runtime. Unlike `#[spec]`, this does not erase the
/// function body or add verification infrastructure.
#[proc_macro_attribute]
pub fn spec_mode(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::spec_mode(attr, item)
}

/// Marks a function for result memoization during proof computation.
#[proc_macro_attribute]
pub fn memoize(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::memoize(attr, item)
}

/// Specifies which tracked invariants a function may open (`any`, `none`, or names).
#[proc_macro_attribute]
pub fn opens_invariants(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::opens_invariants(attr, item)
}

/// Verus-compatible function verifier options such as `nonlinear`.
#[proc_macro_attribute]
pub fn verifier(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::verifier(attr, item)
}

/// Marks a proof function for use in `via` clauses of `#[decreases]`.
#[proc_macro_attribute]
pub fn via_fn(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::via_fn(attr, item)
}

/// Names the return value for use in postconditions (`ret` in `ensures!`).
#[proc_macro_attribute]
pub fn returns(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::returns(attr, item)
}

/// Marks a function body as trusted (not verified, contracts still checked).
#[proc_macro_attribute]
pub fn external_body(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::external_body(attr, item)
}

/// Marks a function or impl block as external/trusted.
#[proc_macro_attribute]
pub fn external(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::external(attr, item)
}

/// Marks a spec function as opaque (body hidden from solver unless revealed).
///
/// Must appear AFTER `#[trust_vc::spec]` so spec expansion can detect it.
#[proc_macro_attribute]
pub fn opaque(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // Pass-through: opaque is a marker read by spec/proof expansion.
    item
}

/// Marks a spec function for call-site body substitution.
///
/// Must appear AFTER `#[trust_vc::spec]` so spec expansion can detect it.
#[proc_macro_attribute]
pub fn inline(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::inline(attr, item)
}

/// Marks an executable helper as callable from specification clauses.
#[proc_macro_attribute]
pub fn allow_in_spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::allow_in_spec(attr, item)
}

/// Interprets an executable helper as a named spec helper in specification clauses.
#[proc_macro_attribute]
pub fn when_used_as_spec(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::when_used_as_spec(attr, item)
}

/// Combined contract attribute for design-by-contract style specifications.
///
/// Accepts `requires`, `ensures`, `returns`, `decreases`, and `cite` clauses:
/// ```ignore
/// #[trust_vc::contract(
///     requires(x > 0, x < 100),
///     cite(monotone(x), "proofs::lemma_4_2"),
///     ensures(ret > x),
///     returns(ret),
/// )]
/// fn foo(x: u32) -> u32 { x + 1 }
/// ```
///
/// A `cite` clause registers an explicitly *trusted* assumption with provenance
/// (assumed, never proven); see [`cite!`].
///
/// Must be the outermost trust_vc attribute (before `#[proof]`, `#[spec]`, etc.).
#[proc_macro_attribute]
pub fn contract(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_entrypoints::contract(attr, item)
}

/// Cites an externally-justified fact as an explicitly *trusted* assumption.
///
/// `cite!(expr)` or `cite!(expr, "reference")` (the reference may also be a path
/// to an external proof/lemma/source). The fact is assumed — added to the
/// assumption base like [`assume!`] — and recorded as trust-tainted with its
/// citation provenance.
///
/// SOUNDNESS: a cited fact is trusted, never proven. It is surfaced as part of
/// the trust surface (e.g. `cargo trust_vc check --no-cheating`) exactly like an
/// axiom/assumption, so any verification relying on it is visibly trust-tainted.
#[proc_macro]
pub fn cite(input: TokenStream) -> TokenStream {
    proof_entrypoints::cite(input)
}

/// Introduces an assumption for proofs (unsound if incorrect).
#[proc_macro]
pub fn assume(input: TokenStream) -> TokenStream {
    proof_entrypoints::assume(input)
}

/// Proof assertion verified by ay (symbolic, not runtime).
#[proc_macro]
pub fn assert(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input.clone());
    if is_verus_assert_forall_by(&tokens) {
        return match trust_vc_core::parse_assert_forall_by(tokens) {
            Ok(parsed) => TokenStream::from(macro_expand::expand_assert_forall_by(parsed)),
            Err(err) => TokenStream::from(err.to_compile_error()),
        };
    }

    proof_entrypoints::assert(input)
}

fn is_verus_assert_forall_by(tokens: &proc_macro2::TokenStream) -> bool {
    let mut iter = tokens.clone().into_iter();
    match iter.next() {
        Some(proc_macro2::TokenTree::Ident(ident)) if ident == "forall" => {
            let starts_with_binder = matches!(
                iter.next(),
                Some(proc_macro2::TokenTree::Punct(punct)) if punct.as_char() == '|'
            );
            starts_with_binder && has_top_level_by_block_after_binder(iter)
        }
        Some(proc_macro2::TokenTree::Ident(ident)) if ident == "assert" => {
            matches!(
                iter.next(),
                Some(proc_macro2::TokenTree::Ident(ident)) if ident == "forall"
            ) && matches!(
                iter.next(),
                Some(proc_macro2::TokenTree::Punct(punct)) if punct.as_char() == '|'
            ) && has_top_level_by_block_after_binder(iter)
        }
        _ => false,
    }
}

fn has_top_level_by_block_after_binder(
    iter: impl IntoIterator<Item = proc_macro2::TokenTree>,
) -> bool {
    let mut seen_closing_pipe = false;
    let mut iter = iter.into_iter().peekable();

    while let Some(tree) = iter.next() {
        if !seen_closing_pipe {
            if matches!(tree, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == '|') {
                seen_closing_pipe = true;
            }
            continue;
        }

        if matches!(&tree, proc_macro2::TokenTree::Ident(ident) if ident == "by") {
            return matches!(
                iter.peek(),
                Some(proc_macro2::TokenTree::Group(group))
                    if group.delimiter() == proc_macro2::Delimiter::Brace
            );
        }
    }

    false
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod tests {
    use quote::quote;

    use super::is_verus_assert_forall_by;

    #[test]
    fn inline_forall_without_by_uses_normal_assert_path() {
        assert!(
            !is_verus_assert_forall_by(&quote! { forall|i: int| i == i }),
            "plain inline forall should not be routed to assert_forall_by"
        );
    }

    #[test]
    fn forall_by_routes_to_assert_forall_by() {
        assert!(
            is_verus_assert_forall_by(&quote! { forall|i: int| i == i by {} }),
            "Verus assert-forall-by syntax should use the proof-block parser"
        );
    }

    #[test]
    fn body_identifier_named_by_is_not_proof_block_syntax() {
        assert!(
            !is_verus_assert_forall_by(&quote! { forall|by: int| by == by }),
            "a binder/body identifier named `by` is not a proof block"
        );
    }
}

/// Proof precondition — must hold on function entry.
#[proc_macro]
pub fn requires(input: TokenStream) -> TokenStream {
    proof_entrypoints::requires(input)
}

/// Soft precondition for spec functions — violations produce warnings, not errors.
/// Part of #2483.
#[proc_macro]
pub fn recommends(input: TokenStream) -> TokenStream {
    proof_entrypoints::recommends(input)
}

/// Ghost precondition — verified but not checked at runtime (ghost types).
#[proc_macro]
pub fn ghost_requires(input: TokenStream) -> TokenStream {
    proof_entrypoints::ghost_requires(input)
}

/// Ghost postcondition — verified but not checked at runtime (ghost types).
#[proc_macro]
pub fn ghost_ensures(input: TokenStream) -> TokenStream {
    proof_entrypoints::ghost_ensures(input)
}

/// Proof postcondition — must hold on function exit. Supports `old!(var)`.
#[proc_macro]
pub fn ensures(input: TokenStream) -> TokenStream {
    proof_entrypoints::ensures(input)
}

/// Inline proof block — verified by trust_mc, erased at runtime.
#[proc_macro]
pub fn proof_block(input: TokenStream) -> TokenStream {
    proof_entrypoints::proof_block(input)
}

/// Universal quantification — asserts a property holds for all values.
///
/// The closure specifies bound variables: `forall!(|i: usize| property(i))`.
#[proc_macro]
pub fn forall(input: TokenStream) -> TokenStream {
    solver_entrypoints::forall(input)
}

/// Existential quantification — asserts a property holds for some value.
///
/// The closure specifies bound variables: `exists!(|i: usize| property(i))`.
#[proc_macro]
pub fn exists(input: TokenStream) -> TokenStream {
    solver_entrypoints::exists(input)
}

/// Item-position non-tokenized state machine (D1a).
///
/// Runs the same parse, well-formedness and admission as the file lane
/// (`trust_vc_core::state_machine_dsl`) and emits the same items plus the
/// compile-only shims (`pub mod NAME { pub use .. as State; }` and associated
/// wrappers) so `NAME::State::…` paths resolve under rustc. A refused machine
/// is a `compile_error!`. Verification happens on the file lane only.
#[proc_macro]
pub fn state_machine(input: TokenStream) -> TokenStream {
    TokenStream::from(trust_vc_core::state_machine_dsl::expand_tokens(
        proc_macro2::TokenStream::from(input),
    ))
}

/// Pre-state value accessor for postconditions.
///
/// Use `old!(expr)` within `ensures!` to refer to the value at function entry.
#[proc_macro]
pub fn old(input: TokenStream) -> TokenStream {
    proof_entrypoints::old(input)
}

/// Lexicographic decrease relation for termination proofs.
///
/// Syntax: `decreases_to!(e1, e2 => f1, f2)`.
#[proc_macro]
pub fn decreases_to(input: TokenStream) -> TokenStream {
    solver_entrypoints::decreases_to(input)
}

/// Tracks a local variable declaration for verification.
#[proc_macro]
pub fn track_let(input: TokenStream) -> TokenStream {
    proof_entrypoints::track_let(input)
}

/// Scoped assumption with proof block.
///
/// Assumes a condition within a local scope. The assumption is visible
/// to assertions within the block but does not propagate outside.
///
/// Two-arg: `assume_by!(condition, { block })` — scoped assumption.
/// Single-arg: `assume_by!(condition)` — alias for `assume!`.
#[proc_macro]
pub fn assume_by(input: TokenStream) -> TokenStream {
    proof_entrypoints::assume_by(input)
}

/// Scoped assertion with proof block.
///
/// Proves an assertion using a local proof block whose effects don't
/// propagate outside the scope.
#[proc_macro]
pub fn assert_by(input: TokenStream) -> TokenStream {
    proof_entrypoints::assert_by(input)
}

/// Scoped universal assertion with a proof block.
///
/// Syntax: `assert_forall_by!(|x: T| condition, { proof_block })`.
#[proc_macro]
pub fn assert_forall_by(input: TokenStream) -> TokenStream {
    proof_entrypoints::assert_forall_by(input)
}

/// Preferred spelling of `assert_by!`.
///
/// Accepts the same single-argument and Verus-style two-argument forms as
/// `assert_by!`.
#[proc_macro]
pub fn assert_with_proof(input: TokenStream) -> TokenStream {
    proof_entrypoints::assert_by(input)
}

/// Proves an assertion by contradiction using a local proof block.
///
/// Syntax: `assert_by_contradiction!(condition, { ... })`.
/// The proof block runs in an `assert_by!` scope with `!condition` assumed.
#[proc_macro]
pub fn assert_by_contradiction(input: TokenStream) -> TokenStream {
    proof_entrypoints::assert_by_contradiction(input)
}

/// Reveals an opaque spec function's body axiom in the current proof context.
///
/// Usage: `trust_vc::reveal!(fn_name);`
#[proc_macro]
pub fn reveal(input: TokenStream) -> TokenStream {
    proof_entrypoints::reveal(input)
}

/// Hides a spec function's body axiom in the current proof context
/// (Verus `hide(f)` — the inverse of `reveal!`).
///
/// The function becomes strictly uninterpreted for this proof — exactly like
/// an unrevealed `#[trust_vc::opaque]` spec fn — unless the same proof also
/// `reveal!`s it (reveal wins over hide, matching the net effect of upstream
/// Verus's flow-ordered `hide(f); …; reveal(f)`).
///
/// Usage: `trust_vc::hide!(fn_name);`
#[proc_macro]
pub fn hide(input: TokenStream) -> TokenStream {
    proof_entrypoints::hide(input)
}

/// Activates a named broadcast group in the current proof context.
///
/// Usage: `trust_vc::broadcast_use!(group_name);`
#[proc_macro]
pub fn broadcast_use(input: TokenStream) -> TokenStream {
    proof_entrypoints::broadcast_use(input)
}

/// Defines or reveals a named group of opaque functions.
///
/// Named definition: `trust_vc::reveal_group!(group_name { fn1, fn2, fn3 });`
/// must appear at module scope so the crate can emit a manifest entry.
/// Inline reveal (legacy): `trust_vc::reveal_group!(fn1, fn2, fn3);`
/// Then use `trust_vc::reveal!(group_name)` or `trust_vc::broadcast_use!(group_name)`.
#[proc_macro]
pub fn reveal_group(input: TokenStream) -> TokenStream {
    proof_entrypoints::reveal_group(input)
}

/// Calculational proof block for chain-of-reasoning proofs.
///
/// Desugars into sequential `assert_by!` calls with a transitive conclusion.
/// ```ignore
/// trust_vc::calc! {
///     a; == { lemma_a_eq_b(); } b; <= {} c;
/// }
/// // Conclusion available: a <= c
/// ```
#[proc_macro]
pub fn calc(input: TokenStream) -> TokenStream {
    proof_entrypoints::calc(input)
}

/// Assert using nonlinear arithmetic solver.
///
/// Uses specialized solver for `*`, `/`, `%` with symbolic values.
#[proc_macro]
pub fn assert_by_nonlinear(input: TokenStream) -> TokenStream {
    solver_entrypoints::assert_by_nonlinear(input)
}

/// Assert using bitvector solver.
///
/// Uses specialized solver for bitwise operations and finite-width integers.
#[proc_macro]
pub fn assert_by_bit_vector(input: TokenStream) -> TokenStream {
    solver_entrypoints::assert_by_bit_vector(input)
}

/// Assert by computation (symbolic evaluation).
///
/// Proves assertion by reducing the expression. Use `only` suffix to require
/// complete reduction to `true`.
#[proc_macro]
pub fn assert_by_compute(input: TokenStream) -> TokenStream {
    solver_entrypoints::assert_by_compute(input)
}

/// Loop invariant declaration.
///
/// Must hold at start of each iteration. Verified inductively by ay.
#[proc_macro]
pub fn invariant(input: TokenStream) -> TokenStream {
    solver_entrypoints::invariant(input)
}

/// Loop invariant that may be violated at break points.
///
/// Verified inductively like `invariant!`, but NOT available as a
/// post-loop assumption. Only holds after normal loop exit (guard false).
/// Part of #2417.
#[proc_macro]
pub fn invariant_except_break(input: TokenStream) -> TokenStream {
    solver_entrypoints::invariant_except_break(input)
}

/// Loop postcondition — must hold on loop exit.
///
/// Verified by assuming all loop invariants hold. Part of #2417.
#[proc_macro]
pub fn loop_ensures(input: TokenStream) -> TokenStream {
    solver_entrypoints::loop_ensures(input)
}

/// Loop variant (termination measure) for loop decreases clause.
///
/// Must be non-negative and strictly decrease each iteration.
#[proc_macro]
pub fn loop_decreases(input: TokenStream) -> TokenStream {
    solver_entrypoints::loop_decreases(input)
}

/// Witness extraction from existential quantifier (Hilbert choice).
///
/// Returns a value satisfying the predicate if one exists, otherwise arbitrary.
/// Same textual expression yields same witness within one verification query.
///
/// Syntax: `choose!(|x: i32| x >= 5)` returns some `i32` where `x >= 5`.
#[proc_macro]
pub fn choose(input: TokenStream) -> TokenStream {
    solver_entrypoints::choose(input)
}

/// Nondeterministic value — unconstrained symbolic constant.
///
/// Returns a completely unconstrained value of type T. In the verification
/// context, the variable bound to this value has no constraints and can take
/// any value in its type's domain. Use `assume!` to add constraints.
///
/// Syntax: `let x: i32 = trust_vc::arbitrary!(i32);`
///
/// At runtime, returns `Default::default()`. Part of #2518.
#[proc_macro]
pub fn arbitrary(input: TokenStream) -> TokenStream {
    solver_entrypoints::arbitrary(input)
}

/// Closure with verification contracts (requires/ensures).
///
/// Rewrites a closure literal with optional `requires(...)` and
/// `ensures(|res| ...)` clauses into a standard Rust closure that collects
/// proof obligations through the existing verification pipeline.
///
/// ```ignore
/// let f = trust_vc::closure!(
///     |x: u64| -> u64
///     requires(x < 128)
///     ensures(|res: u64| res == 2 * x)
///     { 2 * x }
/// );
/// ```
#[proc_macro]
pub fn closure(input: TokenStream) -> TokenStream {
    let tokens = proc_macro2::TokenStream::from(input);
    TokenStream::from(closure_expand::expand_closure(tokens))
}

/// Extensional equality comparison for collections (Verus `=~=` operator).
#[proc_macro]
pub fn ext_eq(input: TokenStream) -> TokenStream {
    solver_entrypoints::ext_eq(input)
}

/// Extensional inequality comparison for collections (negation of `ext_eq!`).
#[proc_macro]
pub fn ext_ne(input: TokenStream) -> TokenStream {
    solver_entrypoints::ext_ne(input)
}

/// Strict equality comparison that bypasses collection extensional equality.
#[proc_macro]
pub fn strict_eq(input: TokenStream) -> TokenStream {
    solver_entrypoints::strict_eq(input)
}

/// Verus-compatible spelling for strict equality (`equal(a, b)` as `equal!(a, b)`).
#[proc_macro]
pub fn equal(input: TokenStream) -> TokenStream {
    solver_entrypoints::equal(input)
}

/// Verus-style sequence extensional equality assertion.
///
/// Syntax: `assert_seqs_equal!(lhs == rhs)`.
#[proc_macro]
pub fn assert_seqs_equal(input: TokenStream) -> TokenStream {
    solver_entrypoints::assert_seqs_equal(input)
}

/// Specify contracts for external functions (e.g., standard library, FFI).
#[proc_macro]
pub fn extern_spec(input: TokenStream) -> TokenStream {
    bridge_entrypoints::extern_spec(input)
}

/// Preferred spelling of `extern_spec!`.
#[proc_macro]
pub fn external_spec(input: TokenStream) -> TokenStream {
    bridge_entrypoints::extern_spec(input)
}

/// Opens a local invariant for the duration of a ghost block.
///
/// Syntax: `open_local_invariant!(&inv => inner => { body })`.
///
/// The invariant predicate is assumed at entry and asserted at exit.
/// The `inner` binding gives mutable access to the tracked inner value.
/// At runtime, the entire block is elided (invariant interactions are ghost-only).
#[proc_macro]
pub fn open_local_invariant(input: TokenStream) -> TokenStream {
    proof_entrypoints::open_local_invariant(input)
}

/// Protocol state machine for ty model checking.
#[proc_macro_attribute]
pub fn protocol(attr: TokenStream, item: TokenStream) -> TokenStream {
    bridge_entrypoints::protocol(attr, item)
}

/// Protocol action — maps to a TY Next disjunct.
#[proc_macro_attribute]
pub fn action(attr: TokenStream, item: TokenStream) -> TokenStream {
    bridge_entrypoints::action(attr, item)
}

/// Safety invariant checked by ty model checker.
#[proc_macro_attribute]
pub fn safety(attr: TokenStream, item: TokenStream) -> TokenStream {
    bridge_entrypoints::safety(attr, item)
}

/// Liveness property with fairness specification.
#[proc_macro_attribute]
pub fn liveness(attr: TokenStream, item: TokenStream) -> TokenStream {
    bridge_entrypoints::liveness(attr, item)
}
