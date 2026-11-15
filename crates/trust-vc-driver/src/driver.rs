//! The real rustc-driver front end (feature = "rustc-driver", NIGHTLY only).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Status: Slice 0 + Slice 2 + Slice 3a + Slice 3b + Slice 3c (+ attribute-block peeling) — scalar Hoare + quantifiers + scalar structs + enums/match + opaque type-param sort
//!
//! ## Slice 3c — the opaque type-parameter sort (Verus-style parametric verification)
//!
//! A free TYPE parameter `T` is verified ONCE over a fresh UNINTERPRETED sort
//! (`map_opaque_type_param` ⇒ `TrustVcType::TypeParam`, which the encoder erases
//! to `Sort::Uninterpreted("Poly")`). A property proven over that free sort holds
//! for ALL concrete `T`, because any concrete type is a model of the free theory
//! over an uninterpreted sort (the congruence argument on [`lower_spec_equality`]).
//! Free CONST parameters stay refused (const-generic monomorphization is a value,
//! not a sort). The ONLY operations that reach a `T` value are those sound in the
//! free theory: EUF equality (the `spec_eq`/`spec_ne` markers → raw solver `=`),
//! field projection of a `T` field (selector), and passing `T` by value. Every
//! STRUCTURE-assuming use surfaces as a trait-method `Call` (ordering, arithmetic,
//! `Clone`/`Copy`/`Default`) or an unmodeled node (cast, tuple/reference position)
//! and FAILS CLOSED. There is NO syn oracle for the opaque sort (syn cannot
//! resolve `ty::Param`), so this fail-closed boundary is the soundness firewall.
//!
//! Datatype CONSTRUCTION with an opaque field (`S { f: x }` where `f: T`) is
//! deliberately fail-closed too — not for soundness, but because it emits a
//! `var == constructor` datatype assumption that trips a panic in ay's datatype
//! `check_sat_assuming` path over the uninterpreted sort (caught → `Unknown`);
//! see the guard in [`lower_adt_construct`]. Scalar/concrete datatype
//! construction is unaffected.
//!
//! ## Attribute-block peeling (real `#[trust_vc::contract]` / `#[trust_vc::proof]` surface)
//!
//! Under `--cfg trust_vc_driver` the `#[trust_vc::contract(requires(..),
//! ensures(..), returns(ret))]` macro expands the function body into an OUTER
//! transparent wrapper block whose sole content is an INNER contract block
//! `{ requires(..); let ret = '__trust_vc_contract_return: { <body> }; ensures(..); ret }`
//! (the `returns(..)` pass adds the outer wrapper; the `let ret` initializer is a
//! LABELED block, the label carrying early `return`s as breaks). [`lower_fn`]
//! scans the DIRECT statements of the body block, so it (1) peels the transparent
//! outer wrapper ([`peel_transparent_body_block`]) to reach the markers and
//! (2) peels the labeled value-block `let` initializer to its tail
//! ([`peel_value_block`]). Both use the same transparent-block discipline as
//! [`peel_quantifier_block`]: only a block whose value provably EQUALS what is
//! lowered is peeled; a value-break, a side-effecting/extra statement, or any
//! unhandled node fails CLOSED to [`DriverError::UnsupportedContract`].
//!
//! This module compiles **only** against the Trust toolchain's `rustc_private`
//! crates, which its sysroot serves (a dev channel, so no `RUSTC_BOOTSTRAP` is
//! needed). It is excluded from the default build so that the load-bearing
//! [`crate::lower`] seam stays portable and cheap.
//!
//! It obtains a [`TyCtxt`] via `rustc_driver::Callbacks`, walks each function's
//! **fully type-checked THIR**, and lowers the *scalar Hoare fragment* into a
//! [`DriverFn`] that the stable lowering seam verifies through the real encoder
//! and ay. The fragment is a strict **whitelist** (Slices 0 + 2 of
//! the internal Verus-replacement plan):
//!
//! * types: `bool`, `i*`/`u*`/`usize`/`isize`;
//! * predicate/arith ops `== != < <= > >=`, `+ - *`, `/ %` (exec fixed-width,
//!   so division-by-zero and overflow are *asserted*, never folded), `&& || !`;
//! * `requires(..)` / `ensures(..)` marker calls;
//! * straight-line **pure** bodies: `let` bindings + a returned local;
//! * **scalar quantifiers** (Slice 2): `forall(|x: T| body)` / `exists(|x: T| body)`
//!   marker calls with a **single TYPED scalar binder** (`bool`, `i*`/`u*`, or the
//!   spec math-integers `int`/`nat` → encoder `MathInt`/`Nat`). The bound var +
//!   sort become a real `∀`/`∃` [`TrustVcExpr::Quantifier`]; the closure body is
//!   lowered through the *same* whitelist (with spec-int operator-overload method
//!   calls `<`/`+`/… on `int`/`nat` lowered to unbounded math arith/compare).
//!   Untyped/inferred, pattern, tuple, or multi-binder closures and any
//!   out-of-fragment body **fail closed** — never synthesized to `true`.
//! * **scalar structs** (Slice 3a): a **non-recursive, non-generic, named-field
//!   struct whose every field is scalar** (`bool`/`i*`/`u*`/`int`/`nat`) maps to a
//!   single-variant `TrustVcType::Datatype` (mirroring the syn front end's
//!   `StructDef`/`register_datatype`). Construction `S { f: e, .. }`
//!   (`ExprKind::Adt`) lowers to the encoder datatype **constructor**
//!   (`variant_symbol_name` ⇒ `FnCall`), and field projection `s.f`
//!   (`ExprKind::Field`) to the **selector** (`selector_symbol_name` ⇒ `FnCall`);
//!   the struct is declared to the encoder via the struct-typed binding so the
//!   native datatype theory supplies the constructor/selector roundtrip.
//! * **scalar enums + simple match** (Slice 3b): a **non-recursive, non-generic
//!   enum** whose every variant is unit or carries only scalar fields maps to a
//!   multi-variant `TrustVcType::Datatype`. Variant construction `E::A` / `E::B(a)`
//!   (`ExprKind::Adt` with the source `variant_index`) lowers to the encoder
//!   **constructor**, and a `match e { … }` (`ExprKind::Match`) on such an enum
//!   with **exactly one bare-variant arm per variant** lowers to the encoder
//!   datatype **match** (ite over per-variant testers, payload read through the
//!   selectors), mirroring the syn front end's `lower_match`. Match **guards**,
//!   wildcard/default arms, or-patterns, literal/range/nested/`ref`/`@`
//!   sub-patterns, `..` rest, non-exhaustive or over-covered matches, tuple/unit
//!   structs, unions, generic or recursive datatypes, non-scalar (incl.
//!   nested-datatype) fields, and `..base`/default-field updates **fail closed** —
//!   a dropped arm or field constraint would be a too-strong VC.
//!
//! Everything else — collections, traits, non-quantifier closures,
//! loops, mutable references, `decreases`, free const params, casts,
//! ordering/arithmetic/trait-method calls on a type-param value, general
//! calls, control flow — is **fail-closed** to
//! [`DriverError::UnsupportedContract`]/[`DriverError::UnsupportedType`]. A
//! dropped construct would yield a *too-strong* VC (proving more than the
//! program), so any unhandled THIR node refuses rather than emitting a vacuous
//! proof. This is a new VC producer; soundness is the paramount constraint.
//! Synthesizing a constant `true` for an unhandled quantifier (the `bitvector.rs`
//! faked-`forall` trap) would be a false-Verify, so it is categorically refused.
//!
//! ## API-stability caveat
//!
//! `rustc_private` is unstable and its surface drifts between compiler builds.
//! This code targets the Trust toolchain the root `rust-toolchain.toml` pins.
//! When the toolchain moves, expect to adjust the `Callbacks::after_analysis`
//! signature, the HIR
//! item-iteration API, `fn_sig`/`generics_of`, and the THIR accessors
//! (`thir_body`, `ExprKind`, `StmtKind`, `PatKind`, `hir_name`).

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_abi::Size;
use rustc_ast::ast::LitKind;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface::Compiler;
use rustc_middle::mir::{BinOp, UnOp};
use rustc_middle::thir::{
    self, AdtExprBase, BlockId, ExprId, ExprKind, LogicalOp, PatKind, StmtKind, Thir,
};
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt};

use crate::lower::{Binding, DriverFn, Outcome};
use trust_vc_core::ir::{
    ArithOp, CompareOp, DatatypeVariant, LogicOp, MatchArm, MatchPattern, QuantifierKind,
    TrustVcExpr, TrustVcType,
};

/// `-Z` flag that makes THIR-consuming passes (notably `check_unsafety`) *borrow*
/// rather than **steal** the THIR, so it survives to `after_analysis`. Without
/// it `tcx.thir_body(..)` panics with "attempted to read from stolen value".
/// `run` injects this automatically; the Trust compiler's dev channel accepts
/// the `-Z` flag without `RUSTC_BOOTSTRAP`.
const NO_STEAL_THIR: &str = "-Zno-steal-thir";

/// The cfg the trust_vc contract macros key their bare-marker surface bridge on.
/// `run` injects `--cfg trust_vc_driver` so that a real corpus file's
/// `requires!`/`ensures!`/`forall!`/`exists!` expand to
/// `trust_vc_core::__driver_markers::{requires,ensures,forall,exists}` CALLS
/// (which this driver recognizes by `callee_name` and lowers), rather than the
/// default runtime `assert!` / vacuous `true`. Under this cfg the macro arms are
/// mutually exclusive, so no vacuous `true` is emitted alongside a marker.
const DRIVER_CFG: &str = "trust_vc_driver";

/// Reasons a function could not be lowered by the driver. Every variant is a
/// *fail-closed* outcome: the driver never reports success for a function it
/// could not fully and faithfully encode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DriverError {
    /// A parameter, local, or return type is outside the scalar fragment.
    UnsupportedType(String),
    /// The function carries `requires`/`ensures`/body content the THIR walker
    /// does not lower within the scalar Hoare fragment. Fail-closed: this is a
    /// refusal, never a vacuous proof.
    UnsupportedContract(String),
}

/// One verification result collected during a compiler run.
#[derive(Debug, Clone)]
pub struct DriverResult {
    /// The verified function's name.
    pub function: String,
    /// `Ok(outcome)` when the function was fully lowered and checked; `Err` when
    /// it was skipped fail-closed (with the reason).
    pub result: Result<Outcome, DriverError>,
}

/// `rustc_driver::Callbacks` implementation that runs trust-vc verification after
/// rustc's analysis passes complete (so types, traits, and borrows are resolved).
#[derive(Default)]
pub struct TrustVcCallbacks {
    /// Results accumulated across all verification-target functions in the crate.
    pub results: Vec<DriverResult>,
}

impl Callbacks for TrustVcCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        // THIR survives to here because `run` injects `-Zno-steal-thir`. Walk
        // each free function; `lower_fn` returns `Ok(None)` for non-targets
        // (no `requires`/`ensures` markers), so helpers and the marker shims are
        // skipped rather than checked.
        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
                continue;
            }
            let def_id = item.owner_id.def_id;
            match lower_fn(tcx, def_id) {
                Ok(Some(driver_fn)) => {
                    // `verify_exec` applies exec arithmetic semantics
                    // (overflow / div0 / shift checks).
                    let outcome = driver_fn.verify_exec().0;
                    self.results.push(DriverResult {
                        function: driver_fn_name(tcx, def_id),
                        result: Ok(outcome),
                    });
                }
                Err(err) => self.results.push(DriverResult {
                    function: driver_fn_name(tcx, def_id),
                    result: Err(err),
                }),
                Ok(None) => {}
            }
        }

        // Verification is a side analysis; let the rest of compilation proceed so
        // the driver behaves like a normal `cargo check`.
        Compilation::Continue
    }
}

/// The function's name for labeling a [`DriverResult`].
fn driver_fn_name(tcx: TyCtxt<'_>, def_id: LocalDefId) -> String {
    tcx.item_name(def_id.to_def_id()).to_string()
}

/// Lowers one function into a [`DriverFn`] over the scalar Hoare fragment.
///
/// Returns `Ok(None)` when the function is **not** a verification target (it
/// carries no `requires`/`ensures` markers), `Ok(Some(_))` when the whole
/// contract + body lowered within the fragment, and `Err(_)` when the function
/// *is* a target but contains something outside the fragment (fail-closed).
fn lower_fn(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Result<Option<DriverFn>, DriverError> {
    let Ok((thir_steal, body_id)) = tcx.thir_body(def_id) else {
        // No analyzable THIR (e.g. an extern/intrinsic shim): not a target.
        return Ok(None);
    };
    let thir = thir_steal.borrow();
    let thir: &Thir<'_> = &thir;

    // The fn body is a block (possibly wrapped in destruction `Scope`s).
    let body_id = peel(thir, body_id);
    let ExprKind::Block { block } = &thir[body_id].kind else {
        return Ok(None);
    };
    // Peel a TRANSPARENT single wrapper block around the fn body. The
    // `#[trust_vc::contract(..)]` / `returns(..)` attribute expansion wraps the
    // real contract block (`{ requires(..); let ret = ..; ensures(..); ret }`)
    // inside an OUTER block whose sole content is that inner block as its tail
    // (the `#[cfg(trust_mc)]` statement is cfg-stripped away). The marker scan +
    // body lowering read the block's DIRECT statements, so without peeling this
    // wrapper the driver sees the outer block's (empty) statement list, finds no
    // `requires`/`ensures` markers, and treats a real attribute-macro function as
    // a non-target (the "0 in-fragment targets" symptom). See
    // [`peel_transparent_body_block`] for the soundness discipline.
    let block = &thir[peel_transparent_body_block(thir, *block)];

    // Pass 1: is this a verification target? (cheap marker scan, no lowering)
    let mut is_target = false;
    for stmt_id in block.stmts.iter() {
        if let StmtKind::Expr { expr, .. } = &thir[*stmt_id].kind {
            if let Some(name) = callee_name(tcx, thir, *expr) {
                if name == "requires" || name == "ensures" {
                    is_target = true;
                    break;
                }
            }
        }
    }
    if !is_target {
        return Ok(None);
    }

    let name = tcx.item_name(def_id.to_def_id()).to_string();

    // Parametric verification over free TYPE parameters (Slice 3c, opaque
    // type-param sort): a free `T` is verified ONCE over a fresh uninterpreted
    // sort (`map_opaque_type_param` ⇒ `TrustVcType::TypeParam`), which proves the
    // property for ALL concrete `T` — any concrete type is a model of the free
    // theory over an uninterpreted sort (see `map_opaque_type_param`). Only the
    // sound free-theory operations reach a `T` value: EUF equality (the `spec_eq`
    // /`spec_ne` markers), field projection of a `T` field, datatype construction
    // with a `T` field, and passing `T` by value; EVERY structure-assuming use
    // (ordering, arithmetic, any trait-method call, cast, …) surfaces as an
    // out-of-fragment THIR node and FAILS CLOSED through the strict whitelist.
    //
    // CONST parameters stay refused: const-generic monomorphization (a value, not
    // a sort) is out of scope, and an unmodeled const would be a too-strong VC.
    let counts = tcx.generics_of(def_id).own_counts();
    if counts.consts > 0 {
        return Err(DriverError::UnsupportedContract(format!(
            "{name}: free const parameters (const-generic monomorphization out of fragment)"
        )));
    }

    // Parameters: names + resolved types straight from THIR.
    let mut declared: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut param_bindings: Vec<Binding> = Vec::new();
    for (idx, param) in thir.params.iter().enumerate() {
        let pname = param
            .pat
            .as_deref()
            .and_then(|p| binding_name(p))
            .unwrap_or_else(|| format!("arg{idx}"));
        let pty = map_local_ty(tcx, param.ty).ok_or_else(|| {
            DriverError::UnsupportedType(format!("param {pname}: {:?}", param.ty))
        })?;
        if !declared.insert(pname.clone()) {
            return Err(DriverError::UnsupportedContract(format!(
                "{name}: parameter name `{pname}` shadows another binding"
            )));
        }
        param_bindings.push(Binding::new(pname, pty));
    }

    // Pass 2: full lowering of the contract + straight-line body.
    let mut requires: Vec<TrustVcExpr> = Vec::new();
    let mut ensures: Vec<TrustVcExpr> = Vec::new();
    // Ordered (name, ty, lowered-initializer) for each `let` binding.
    let mut lets: Vec<(String, TrustVcType, TrustVcExpr)> = Vec::new();

    for stmt_id in block.stmts.iter() {
        match &thir[*stmt_id].kind {
            StmtKind::Let {
                pattern,
                initializer,
                ..
            } => {
                let Some(lname) = binding_name(pattern) else {
                    return Err(DriverError::UnsupportedContract(format!(
                        "{name}: non-trivial `let` pattern out of scalar fragment"
                    )));
                };
                let lty = map_local_ty(tcx, pattern.ty).ok_or_else(|| {
                    DriverError::UnsupportedType(format!("let {lname}: {:?}", pattern.ty))
                })?;
                let Some(init) = initializer else {
                    return Err(DriverError::UnsupportedContract(format!(
                        "{name}: `let {lname}` without initializer (uninitialized binding)"
                    )));
                };
                // The `#[trust_vc::contract]` `returns(..)` rewrite binds the
                // function result through a LABELED value block:
                // `let ret = '__trust_vc_contract_return: { <body> };`. Peel that
                // transparent value block to its tail so the initializer lowers to
                // the body value; [`peel_value_block`] is fail-closed (whitelist),
                // so a value-break or a side-effecting statement refuses here.
                let init = peel_value_block(thir, *init);
                let init_expr = lower_thir_expr(tcx, thir, init)?;
                if !declared.insert(lname.clone()) {
                    return Err(DriverError::UnsupportedContract(format!(
                        "{name}: binding `{lname}` shadows another binding"
                    )));
                }
                lets.push((lname, lty, init_expr));
            }
            StmtKind::Expr { expr, .. } => {
                let peeled = peel(thir, *expr);
                let ExprKind::Call { fun, args, .. } = &thir[peeled].kind else {
                    return Err(DriverError::UnsupportedContract(format!(
                        "{name}: non-call statement in body (possibly impure) out of scalar fragment"
                    )));
                };
                match callee_name(tcx, thir, peeled).as_deref() {
                    Some("requires") => {
                        for a in args.iter() {
                            requires.push(lower_thir_expr(tcx, thir, *a)?);
                        }
                    }
                    Some("ensures") => {
                        for a in args.iter() {
                            ensures.push(lower_thir_expr(tcx, thir, *a)?);
                        }
                    }
                    _ => {
                        let _ = fun;
                        return Err(DriverError::UnsupportedContract(format!(
                            "{name}: call statement is not a requires/ensures marker (possibly impure)"
                        )));
                    }
                }
            }
        }
    }

    // The return value must be a bare local (the canonical `…; result` shape),
    // so postconditions can name it. Anything else is fail-closed.
    let Some(tail_id) = block.expr else {
        return Err(DriverError::UnsupportedContract(format!(
            "{name}: body has no returned scalar value out of scalar fragment"
        )));
    };
    let tail_id = peel(thir, tail_id);
    let ExprKind::VarRef { id } = &thir[tail_id].kind else {
        return Err(DriverError::UnsupportedContract(format!(
            "{name}: return value is not a bare local (out of straight-line scalar fragment)"
        )));
    };
    let result_name = tcx.hir_name(id.0).to_string();
    let result_ty = map_local_ty(tcx, thir[tail_id].ty).ok_or_else(|| {
        DriverError::UnsupportedType(format!("return {result_name}: {:?}", thir[tail_id].ty))
    })?;
    if !declared.contains(&result_name) {
        return Err(DriverError::UnsupportedContract(format!(
            "{name}: returned local `{result_name}` is not a declared binding"
        )));
    }

    // Each `let name = init;` becomes an assumed body relation `name == init`.
    // The returned local's relation is what ties the postcondition to the body.
    let mut params: Vec<Binding> = Vec::new();
    for (lname, lty, linit) in lets {
        requires.push(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::Var {
                name: lname.clone(),
                ty: lty.clone(),
            }),
            right: Box::new(linit),
        });
        if lname != result_name {
            params.push(Binding::new(lname, lty));
        }
    }
    for b in param_bindings {
        if b.name != result_name {
            params.push(b);
        }
    }

    Ok(Some(DriverFn {
        name,
        params,
        result: Binding::new(result_name, result_ty),
        requires,
        body_value: None,
        ensures,
    }))
}

/// Peels destruction `Scope`s and value-preserving no-ops (`Use`, `NeverToAny`)
/// to reach the underlying expression. These never change the value, so peeling
/// them is sound; we deliberately do **not** peel type ascriptions or casts.
fn peel(thir: &Thir<'_>, mut id: ExprId) -> ExprId {
    loop {
        match &thir[id].kind {
            ExprKind::Scope { value, .. } => id = *value,
            ExprKind::Use { source } => id = *source,
            ExprKind::NeverToAny { source } => id = *source,
            _ => return id,
        }
    }
}

/// SCOPED quantifier-block peel (soundness: R-body-relation). The surface
/// `forall!`/`exists!` macros expand, under `--cfg trust_vc_driver`, to a
/// BLOCK-WRAPPED marker rather than a bare marker call:
/// `{ let _c = <typecheck closure>; { forall(<real closure>) } }` — a pure
/// typecheck-aid `let` binding (the driver ignores it: it reads the marker
/// call's own closure arg, never the `let`) plus a tail that yields the real
/// marker call. This peels that SPECIFIC pure shape and returns the innermost
/// tail expression, so [`lower_thir_expr`] can dispatch a marker tail to
/// [`lower_quantifier`].
///
/// **Soundness — whitelist, not blacklist.** A block is peeled ONLY when EVERY
/// statement is a pure `let name = <closure literal>;` (a closure literal has no
/// side effects, and the binding is unused by the tail) and the block has a
/// trailing tail expression. ANY other statement — a non-closure-literal
/// initializer (a call/constructor that could have effects), a `let` without an
/// initializer or with an `else` diverge, or an expression statement (a call /
/// assignment) — or a missing tail, or a labeled block that could `break` to a
/// value other than its tail, makes the whole block refuse (`None`), and the
/// caller then fails closed. We NEVER assume block == tail when a statement
/// could have effects. A nested wrapper block (the inner `{ marker }`) is peeled
/// by the same rule via the loop; the returned id is guaranteed non-`Block`, so
/// the caller inspects the real tail.
///
/// This is deliberately **not** folded into the general [`peel`]: broadening
/// `peel` would peel blocks everywhere (e.g. the function body, `let`
/// initializers), which would be wrong. It is reached only from
/// [`lower_thir_expr`]'s `Block` arm — a predicate/marker-arg position.
fn peel_quantifier_block(thir: &Thir<'_>, id: ExprId) -> Option<ExprId> {
    let mut id = peel(thir, id);
    loop {
        let ExprKind::Block { block } = &thir[id].kind else {
            // Reached a non-block tail (e.g. the marker call): hand it back for
            // the caller to inspect.
            return Some(id);
        };
        let block = &thir[*block];
        // A labeled block could `break 'label val` to a value other than its
        // tail; refuse so "block value == tail value" holds. (The statement/tail
        // whitelist already excludes any `break`, but guard defensively.)
        if block.targeted_by_break {
            return None;
        }
        for stmt_id in block.stmts.iter() {
            let StmtKind::Let {
                pattern,
                initializer: Some(init),
                else_block: None,
                ..
            } = &thir[*stmt_id].kind
            else {
                // Non-`let`, uninitialized `let`, `let`-`else`, or an expression
                // statement — any could have effects. Refuse the whole block.
                return None;
            };
            // Only a simple `let name = ...` binding (the typecheck-aid closure);
            // a destructuring/ascription pattern is out of the whitelisted shape.
            if binding_name(pattern).is_none() {
                return None;
            }
            // The initializer MUST be a closure literal (pure: constructing a
            // closure has no side effects). A call, constructor, or any other
            // initializer could have effects, so refuse.
            if !matches!(&thir[peel(thir, *init)].kind, ExprKind::Closure(_)) {
                return None;
            }
        }
        // A block with no tail yields `()`, not a predicate value — refuse.
        let tail = block.expr?;
        id = peel(thir, tail);
    }
}

/// Peels a TRANSPARENT single wrapper block around the fn body, returning the
/// innermost wrapped block whose statements `lower_fn` then scans.
///
/// The `#[trust_vc::contract(..)]` attribute lowers `requires`/`ensures`/`returns`
/// into a contract block, and the subsequent `returns(..)` pass wraps THAT block
/// inside an outer block whose only content is the inner block as its tail (a
/// `#[cfg(trust_mc)]` statement, stripped under the driver cfg, is the outer
/// block's only would-be statement). So the real markers live in the inner
/// block, one level below the outer body block `lower_fn` first reaches.
///
/// **Soundness — whitelist, transparent-block discipline (same as
/// [`peel_quantifier_block`]).** Descend through a block ONLY when it is a
/// genuine transparent wrapper: NOT `targeted_by_break` (an unlabeled block whose
/// value is unambiguously its tail — a labeled/loop block could `break` to a
/// value other than its tail), has NO statements (nothing to drop, reorder, or
/// that could carry a side effect / early exit), and whose tail — after [`peel`]
/// — is itself a `Block`. Each descent preserves the block value (`{ E }` == E),
/// so the innermost block's statements + tail are exactly the outer body's. Any
/// labeled wrapper, non-empty wrapper, or non-block tail STOPS the descent and
/// the block is scanned as-is, so no statement is ever silently skipped and a
/// non-transparent wrapper simply leaves the function classified as a non-target
/// (fail-closed, never a fabricated verdict).
///
/// Deliberately NOT folded into the general [`peel`]: broadening `peel` would
/// peel blocks everywhere (e.g. `let` initializers), which would be wrong.
fn peel_transparent_body_block(thir: &Thir<'_>, mut block_id: BlockId) -> BlockId {
    loop {
        let block = &thir[block_id];
        // A labeled/loop block (`targeted_by_break`) could break to a value other
        // than its tail; a block with statements could drop/reorder them or carry
        // an effect. Neither is a transparent wrapper — stop and scan as-is.
        if block.targeted_by_break || !block.stmts.is_empty() {
            return block_id;
        }
        let Some(tail) = block.expr else {
            return block_id;
        };
        let ExprKind::Block { block: inner } = &thir[peel(thir, tail)].kind else {
            return block_id;
        };
        block_id = *inner;
    }
}

/// If a `let` initializer is a transparent VALUE block whose value is exactly its
/// tail expression, returns that tail (for lowering); otherwise returns `id`
/// unchanged (so [`lower_thir_expr`] then fails closed on any block it cannot
/// prove transparent). This peels the `let ret = '__trust_vc_contract_return: {
/// <body> };` LABELED block that the contract macro's `returns(..)` rewrite wraps
/// the function body in (the label carries early `return`s as
/// `break '__trust_vc_contract_return <value>`).
///
/// **Soundness — block value == tail, whitelist discipline.** A labeled block is
/// ALWAYS `targeted_by_break` in THIR — rustc sets that flag from
/// `opt_label.is_some()` (ast_lowering `expr.rs`), NOT from whether a `break`
/// actually targets the block — so the flag CANNOT distinguish "labeled" from
/// "actually broken to with a value" and is unusable as the gate here (it would
/// reject every labeled block, defeating the peel). Instead the peel is sound
/// because it (1) requires the block to have NO statements (a `break <value>` /
/// side effect can only reach the block value through a statement or the tail;
/// the empty-statement requirement removes the statement channel) and (2) lowers
/// ONLY the tail through the strict [`lower_thir_expr`] whitelist, which rejects
/// `ExprKind::Break` and every control-flow construct a value-break could ride
/// (`if`/`loop`/`return`). So the sole remaining way the block value could differ
/// from the lowered tail — a reachable `break '<label> <value>` inside the tail —
/// FAILS CLOSED in `lower_thir_expr` rather than being silently dropped. We never
/// assume block == tail when a value-break could make them differ.
fn peel_value_block(thir: &Thir<'_>, id: ExprId) -> ExprId {
    let mut id = peel(thir, id);
    loop {
        let ExprKind::Block { block } = &thir[id].kind else {
            return id;
        };
        let block = &thir[*block];
        // A statement could carry a side effect or a `break <value>`; refuse the
        // peel (lower_thir_expr then fails closed on the whole block).
        if !block.stmts.is_empty() {
            return id;
        }
        let Some(tail) = block.expr else {
            return id;
        };
        id = peel(thir, tail);
    }
}

/// The source name of a simple binding pattern, or `None` for anything richer.
fn binding_name(pat: &thir::Pat<'_>) -> Option<String> {
    match &pat.kind {
        PatKind::Binding { name, .. } => Some(name.to_string()),
        _ => None,
    }
}

/// If `id` resolves (after peeling destruction `Scope`s) to a `Call` of a free
/// function, returns that function's name. Used to recognize `requires`/`ensures`
/// markers, whose call expressions are wrapped in a `Scope` at statement level.
fn callee_name(tcx: TyCtxt<'_>, thir: &Thir<'_>, id: ExprId) -> Option<String> {
    if let ExprKind::Call { fun, .. } = &thir[peel(thir, id)].kind {
        if let ty::FnDef(def_id, _) = thir[*fun].ty.kind() {
            return Some(tcx.item_name(*def_id).to_string());
        }
    }
    None
}

/// Lowers one THIR expression into a [`TrustVcExpr`] over the scalar fragment.
///
/// Strict whitelist: any node not explicitly handled fails closed to
/// [`DriverError::UnsupportedContract`] so nothing is ever silently dropped.
fn lower_thir_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    id: ExprId,
) -> Result<TrustVcExpr, DriverError> {
    let id = peel(thir, id);
    let expr = &thir[id];
    match &expr.kind {
        ExprKind::Literal { lit, neg } => match &lit.node {
            LitKind::Bool(b) => Ok(TrustVcExpr::BoolLit(*b)),
            LitKind::Int(value, _) => {
                let ty = map_ty(expr.ty).ok_or_else(|| {
                    DriverError::UnsupportedType(format!("int literal: {:?}", expr.ty))
                })?;
                let v = value.0 as i128;
                Ok(TrustVcExpr::IntLit {
                    value: if *neg { -v } else { v },
                    ty,
                })
            }
            other => Err(DriverError::UnsupportedContract(format!(
                "literal {other:?} out of scalar fragment"
            ))),
        },
        ExprKind::NonHirLiteral { lit, .. } => {
            let ty = map_ty(expr.ty)
                .ok_or_else(|| DriverError::UnsupportedType(format!("literal: {:?}", expr.ty)))?;
            let width = ty
                .bit_width()
                .ok_or_else(|| DriverError::UnsupportedContract("non-scalar literal".into()))?;
            let size = Size::from_bits(u64::from(width));
            let value = if ty.is_unsigned() {
                lit.to_bits(size) as i128
            } else {
                lit.to_int(size)
            };
            Ok(TrustVcExpr::IntLit { value, ty })
        }
        ExprKind::VarRef { id } => {
            let name = tcx.hir_name(id.0).to_string();
            // `map_local_ty` so a struct-typed local (the receiver of a field
            // projection, or a constructed struct bound to a `let`) lowers to a
            // datatype-sorted `Var`; ordinary scalars are unchanged.
            let ty = map_local_ty(tcx, expr.ty).ok_or_else(|| {
                DriverError::UnsupportedType(format!("var {name}: {:?}", expr.ty))
            })?;
            Ok(TrustVcExpr::Var { name, ty })
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let left = Box::new(lower_thir_expr(tcx, thir, *lhs)?);
            let right = Box::new(lower_thir_expr(tcx, thir, *rhs)?);
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                    let aop = match op {
                        BinOp::Add => ArithOp::Add,
                        BinOp::Sub => ArithOp::Sub,
                        BinOp::Mul => ArithOp::Mul,
                        BinOp::Div => ArithOp::Div,
                        BinOp::Rem => ArithOp::Rem,
                        _ => unreachable!(),
                    };
                    let ty = map_ty(expr.ty).ok_or_else(|| {
                        DriverError::UnsupportedType(format!("arith result: {:?}", expr.ty))
                    })?;
                    Ok(TrustVcExpr::Arith {
                        op: aop,
                        left,
                        right,
                        ty,
                    })
                }
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    let cop = match op {
                        BinOp::Eq => CompareOp::Eq,
                        BinOp::Ne => CompareOp::Ne,
                        BinOp::Lt => CompareOp::Lt,
                        BinOp::Le => CompareOp::Le,
                        BinOp::Gt => CompareOp::Gt,
                        BinOp::Ge => CompareOp::Ge,
                        _ => unreachable!(),
                    };
                    Ok(TrustVcExpr::Compare {
                        op: cop,
                        left,
                        right,
                    })
                }
                other => Err(DriverError::UnsupportedContract(format!(
                    "binary operator {other:?} out of scalar fragment"
                ))),
            }
        }
        ExprKind::LogicalOp { op, lhs, rhs } => {
            let left = Box::new(lower_thir_expr(tcx, thir, *lhs)?);
            let right = Box::new(lower_thir_expr(tcx, thir, *rhs)?);
            let lop = match op {
                LogicalOp::And => LogicOp::And,
                LogicalOp::Or => LogicOp::Or,
            };
            Ok(TrustVcExpr::Logic {
                op: lop,
                left,
                right,
            })
        }
        ExprKind::Unary { op, arg } => {
            let inner = Box::new(lower_thir_expr(tcx, thir, *arg)?);
            match op {
                UnOp::Not if expr.ty.is_bool() => Ok(TrustVcExpr::Not(inner)),
                UnOp::Neg => Ok(TrustVcExpr::Neg(inner)),
                other => Err(DriverError::UnsupportedContract(format!(
                    "unary operator {other:?} out of scalar fragment"
                ))),
            }
        }
        // Field projection `s.f` (Slice 3a) → encoder datatype **selector**.
        ExprKind::Field { .. } => lower_field_access(tcx, thir, id),
        // Struct / enum-variant construction `S { f: e }` / `E::V(a)` / `E::V`
        // (Slice 3a struct + Slice 3b enum) → encoder datatype **constructor**.
        ExprKind::Adt(adt_expr) => lower_adt_construct(tcx, thir, expr.ty, adt_expr),
        // `match e { … }` on an enum scrutinee (Slice 3b) → encoder datatype
        // **match** (ite over per-variant testers, payload via selectors).
        ExprKind::Match { .. } => lower_match(tcx, thir, id),
        // A BLOCK-WRAPPED quantifier marker (the `forall!`/`exists!` macro surface
        // shape under `--cfg trust_vc_driver`): `{ let _c = <closure>; { forall(..) } }`.
        // Peel the SPECIFIC pure wrapper (pure closure-literal `let`s + tail
        // marker call) and lower the REAL quantifier via [`lower_quantifier`].
        // Soundness: a block with ANY side-effecting statement, or whose tail is
        // not a `forall`/`exists` marker, FAILS CLOSED here — never a fabricated
        // verdict and never a block whose value could differ from its tail.
        ExprKind::Block { .. } => {
            if let Some(tail) = peel_quantifier_block(thir, id) {
                match callee_name(tcx, thir, tail).as_deref() {
                    Some("forall") => {
                        return lower_quantifier(tcx, thir, tail, QuantifierKind::Forall)
                    }
                    Some("exists") => {
                        return lower_quantifier(tcx, thir, tail, QuantifierKind::Exists)
                    }
                    _ => {}
                }
            }
            Err(DriverError::UnsupportedContract(
                "block expression out of scalar Hoare/quantifier fragment (only a pure \
                 quantifier-marker wrapper block is peeled)"
                    .into(),
            ))
        }
        ExprKind::Call { fun, args, .. } => {
            // (1) `forall(..)` / `exists(..)` marker → real ∀/∃ quantifier (Slice 2).
            //     Recognized here (rather than only at the requires/ensures seam) so
            //     a quantifier can appear nested inside a predicate as well.
            match callee_name(tcx, thir, id).as_deref() {
                Some("forall") => return lower_quantifier(tcx, thir, id, QuantifierKind::Forall),
                Some("exists") => return lower_quantifier(tcx, thir, id, QuantifierKind::Exists),
                // (1b) `spec_eq(a, b)` / `spec_ne(a, b)` — the SPEC-EQUALITY markers
                //      (mathematical `==` / `!=`). These are the SOLE surface through
                //      which EUF equality on an opaque type-param value enters the VC:
                //      Rust's `==`/`!=` on a generic `T` desugar to a `PartialEq`
                //      TRAIT method call (which fails closed — a concrete `PartialEq`
                //      impl need NOT be the mathematical congruence, so treating it as
                //      `=` would be unsound). Spec equality, by contrast, IS the
                //      mathematical equality of `T` — a genuine congruence for every
                //      concrete `T` — so lowering it to a raw solver `=` (`Compare`)
                //      over the uninterpreted sort is sound for ALL `T` (any concrete
                //      `T`'s equality is the identity on its own domain, a model of the
                //      free EUF theory). Recognized by bare `item_name`, exactly like
                //      `requires`/`ensures`/`forall`/`exists`.
                Some("spec_eq") => return lower_spec_equality(tcx, thir, id, CompareOp::Eq),
                Some("spec_ne") => return lower_spec_equality(tcx, thir, id, CompareOp::Ne),
                _ => {}
            }
            // (2) spec-int (`int`/`nat`) operator-overload method call: `<`,`+`,… on a
            //     math-integer become unbounded math arith/compare. Gated on the
            //     receiver (`Self`) type being the spec integer ADT, so this never
            //     reinterprets operators on any other type.
            if let ty::FnDef(def_id, generics) = thir[*fun].ty.kind() {
                if let Some(e) = try_lower_spec_int_op(tcx, thir, *def_id, generics, args)? {
                    return Ok(e);
                }
            }
            // (3) anything else (a general call) is outside the fragment.
            Err(DriverError::UnsupportedContract(
                "call expression out of scalar Hoare/quantifier fragment".into(),
            ))
        }
        _ => Err(DriverError::UnsupportedContract(
            "expression out of scalar Hoare fragment".into(),
        )),
    }
}

/// The spec math-integer flavor of a binder/operand type: Verus `int` (unbounded
/// `MathInt`) or `nat` (`Nat`, `>= 0`). These arrive in THIR as nominal ADTs (the
/// `vstd`/`builtin` types, or the standalone marker shims), so [`map_ty`] returns
/// `None` for them — they are recognized *only* in the quantifier-binder and
/// spec-int-operator positions, never as ordinary parameter/return types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SpecInt {
    /// Verus `int` → [`TrustVcType::MathInt`] (unbounded).
    Int,
    /// Verus `nat` → [`TrustVcType::Nat`] (unbounded, `>= 0` — the encoder emits
    /// the lower-bound range guard for a `Nat`-sorted bound var).
    Nat,
}

impl SpecInt {
    /// The encoder sort for this spec integer.
    fn sort(self) -> TrustVcType {
        match self {
            SpecInt::Int => TrustVcType::MathInt,
            SpecInt::Nat => TrustVcType::Nat,
        }
    }
}

/// Recognizes the spec math-integer ADTs by name (`int` / `nat`). This is the
/// Verus-surface convention (these names are reserved spec types); the driver
/// reinterprets their operators as math arithmetic *only* in spec-int positions.
fn spec_int_kind(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Option<SpecInt> {
    if let ty::Adt(adt, _) = ty.kind() {
        match tcx.item_name(adt.did()).to_string().as_str() {
            "int" => return Some(SpecInt::Int),
            "nat" => return Some(SpecInt::Nat),
            _ => {}
        }
    }
    None
}

/// Maps a **quantifier binder** type into a [`TrustVcType`]. Unlike [`map_ty`],
/// this also accepts the spec math-integers `int`/`nat` (→ `MathInt`/`Nat`).
/// Restricted to binder positions: ordinary `int`/`nat` params/returns remain
/// out of fragment (Slice 0 is monomorphic fixed-width + bool).
fn map_binder_ty(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Option<TrustVcType> {
    if let Some(k) = spec_int_kind(tcx, ty) {
        return Some(k.sort());
    }
    map_ty(ty)
}

/// Lowers a `forall(|x: T| body)` / `exists(|x: T| body)` marker call into a real
/// [`TrustVcExpr::Quantifier`] over the scalar fragment.
///
/// **Soundness (R-quant), strict whitelist:** the binder must be a *single TYPED
/// scalar* (`bool`/`i*`/`u*`/`int`/`nat`); untyped/inferred, pattern, tuple, or
/// multi-binder closures fail closed. The closure body is lowered through
/// [`lower_thir_expr`] (over the closure's own THIR), so an out-of-fragment body
/// refuses the **whole** quantifier — never a synthesized `true` (the
/// `bitvector.rs` faked-`forall` trap, a false-Verify).
fn lower_quantifier<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    call_id: ExprId,
    kind: QuantifierKind,
) -> Result<TrustVcExpr, DriverError> {
    let ExprKind::Call { args, .. } = &thir[peel(thir, call_id)].kind else {
        return Err(DriverError::UnsupportedContract(
            "quantifier marker is not a call".into(),
        ));
    };
    if args.len() != 1 {
        return Err(DriverError::UnsupportedContract(
            "quantifier marker takes exactly one closure argument".into(),
        ));
    }
    let ExprKind::Closure(closure) = &thir[peel(thir, args[0])].kind else {
        return Err(DriverError::UnsupportedContract(
            "quantifier argument is not a closure literal".into(),
        ));
    };
    let closure_def: LocalDefId = closure.closure_id;

    // TYPED binders only: reject inferred/untyped binders via the closure's HIR
    // signature (THIR types are always resolved, so the `|x| ..` vs `|x: T| ..`
    // distinction is only visible in HIR). A single binder is required.
    let rustc_hir::Node::Expr(hir_expr) = tcx.hir_node_by_def_id(closure_def) else {
        return Err(DriverError::UnsupportedContract(
            "quantifier closure has no HIR node".into(),
        ));
    };
    let rustc_hir::ExprKind::Closure(hir_closure) = &hir_expr.kind else {
        return Err(DriverError::UnsupportedContract(
            "quantifier closure HIR is not a closure".into(),
        ));
    };
    let hir_inputs = hir_closure.fn_decl.inputs;
    if hir_inputs.len() != 1 {
        return Err(DriverError::UnsupportedContract(
            "quantifier closure must have exactly one binder (multi-binder out of fragment)".into(),
        ));
    }
    if matches!(hir_inputs[0].kind, rustc_hir::TyKind::Infer(_)) {
        return Err(DriverError::UnsupportedContract(
            "quantifier binder is untyped/inferred (typed scalar binders only)".into(),
        ));
    }

    // The closure body lives in its OWN THIR body, indexed by the closure def-id.
    let Ok((cbody_steal, cbody_id)) = tcx.thir_body(closure_def) else {
        return Err(DriverError::UnsupportedContract(
            "quantifier closure body is unavailable".into(),
        ));
    };
    let cbody = cbody_steal.borrow();
    let cthir: &Thir<'_> = &cbody;

    // Closure THIR params are `[env, binder]`; index 1 is the user binder.
    if cthir.params.len() != 2 {
        return Err(DriverError::UnsupportedContract(
            "quantifier closure binder shape out of fragment (expected one binder)".into(),
        ));
    }
    let Some(binder) = cthir.params.iter().nth(1) else {
        return Err(DriverError::UnsupportedContract(
            "quantifier closure has no binder param".into(),
        ));
    };
    let Some(binder_pat) = binder.pat.as_deref() else {
        return Err(DriverError::UnsupportedContract(
            "quantifier binder has no pattern".into(),
        ));
    };
    let Some(bname) = binding_name(binder_pat) else {
        return Err(DriverError::UnsupportedContract(
            "quantifier binder is a non-trivial pattern (tuple/struct binder out of fragment)"
                .into(),
        ));
    };
    let bty = map_binder_ty(tcx, binder.ty).ok_or_else(|| {
        DriverError::UnsupportedType(format!("quantifier binder {bname}: {:?}", binder.ty))
    })?;

    // Lower the REAL closure body (whitelist). An out-of-fragment body propagates
    // `Err` and refuses the whole quantifier — never a fabricated constant.
    let body = lower_thir_expr(tcx, cthir, cbody_id)?;

    Ok(TrustVcExpr::Quantifier {
        kind,
        bound_vars: vec![(bname, bty)],
        body: Box::new(body),
        // No trigger extraction yet (Slice 2 lowers the binder + body); the
        // encoder infers triggers. Conservative default mode.
        triggers: None,
        trigger_inference_mode: None,
    })
}

/// Lowers a `spec_eq(a, b)` / `spec_ne(a, b)` **spec-equality marker** call into a
/// [`TrustVcExpr::Compare`] `Eq`/`Ne` — a raw solver equality over whatever sort
/// `a`/`b` map to (scalar, datatype, or the opaque type-param `Poly`).
///
/// **Soundness — the free-theory congruence argument (paramount; no oracle).**
/// Spec equality is the *mathematical* equality of the operands' type: reflexive,
/// symmetric, transitive, and a congruence w.r.t. every function (constructors,
/// selectors, …). The solver's `=` over the uninterpreted type-param sort is the
/// FREE such congruence. A VC proven with this `=` over the uninterpreted sort is
/// therefore valid in EVERY model — in particular the model where the sort's
/// domain is a concrete type `T`'s value set and `=` is `T`'s own mathematical
/// equality (the identity on that domain). Hence a property proven for the opaque
/// sort holds for ALL `T`. This is exactly what Rust's `==` (a `PartialEq` trait
/// call, deliberately fail-closed) does NOT license: an arbitrary `PartialEq`
/// impl need not be a congruence, so it is refused. Only spec equality is lowered
/// to `=`.
///
/// Strict shape: exactly two operands (a binary equality), each lowered through
/// the whitelist [`lower_thir_expr`] after peeling the argument auto-reference
/// (`spec_eq(&a, &b)` — the by-reference marker shape that avoids moving a
/// non-`Copy` `T`). An out-of-fragment operand refuses the whole predicate.
fn lower_spec_equality<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    call_id: ExprId,
    op: CompareOp,
) -> Result<TrustVcExpr, DriverError> {
    let ExprKind::Call { args, .. } = &thir[peel(thir, call_id)].kind else {
        return Err(DriverError::UnsupportedContract(
            "spec-equality marker is not a call".into(),
        ));
    };
    let [lhs, rhs] = args.as_ref() else {
        return Err(DriverError::UnsupportedContract(
            "spec-equality marker takes exactly two operands".into(),
        ));
    };
    // Peel the operand reference(s) down to the compared PLACE value. A
    // by-reference marker `spec_eq(&a, &b)` renders each operand in THIR as a
    // shared borrow of the place — commonly the reborrow artifact `&*&place`
    // (`Borrow(Deref(Borrow(place)))`) — whose net value is just `place`.
    let left = Box::new(lower_thir_expr(tcx, thir, peel_place_ref(thir, *lhs))?);
    let right = Box::new(lower_thir_expr(tcx, thir, peel_place_ref(thir, *rhs))?);
    Ok(TrustVcExpr::Compare { op, left, right })
}

/// Peels the reference layers around a spec-equality operand down to the compared
/// PLACE value: `spec_eq(&a, &b)` renders each operand as a shared borrow of a
/// place, often the reborrow artifact `&*&place` = `Borrow(Deref(Borrow(place)))`
/// (net value `place`). Peels destruction `Scope`s/`Use`, a shared `Borrow`, and
/// the reborrow `Deref(Borrow(_))`; a GENUINE `Deref` of any other reference is
/// left in place so it fails closed downstream (never silently dropped), and a
/// reference-typed leaf likewise fails closed in [`map_local_ty`]. `*&place ==
/// place`, so collapsing the reborrow is value-preserving.
fn peel_place_ref(thir: &Thir<'_>, id: ExprId) -> ExprId {
    let mut id = peel(thir, id);
    loop {
        match &thir[id].kind {
            ExprKind::Borrow { arg, .. } => id = peel(thir, *arg),
            ExprKind::Deref { arg } => {
                let inner = peel(thir, *arg);
                match &thir[inner].kind {
                    ExprKind::Borrow { arg: borrowed, .. } => id = peel(thir, *borrowed),
                    // A real dereference (not a `*&place` reborrow): leave it so
                    // the caller fails closed rather than dropping the deref.
                    _ => return id,
                }
            }
            _ => return id,
        }
    }
}

/// If `def_id` (with `generics`) is an arithmetic/comparison **operator trait
/// method whose `Self` is the spec integer ADT** (`int`/`nat`), lowers the call
/// into a math-integer [`TrustVcExpr::Arith`]/[`TrustVcExpr::Compare`]. Returns
/// `Ok(None)` when it is not such a method (the caller then fails closed), so this
/// never reinterprets operators on any non-spec-int type.
///
/// Spec `int`/`nat` arithmetic is **unbounded** (no overflow); `+ - *` map to math
/// `Arith`. `/ %` are deliberately *not* handled (spec div/mod-by-zero is
/// unspecified — folding it would prove more than the program), so they fail
/// closed. Comparisons map to `Compare`.
fn try_lower_spec_int_op<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    generics: GenericArgsRef<'tcx>,
    args: &[ExprId],
) -> Result<Option<TrustVcExpr>, DriverError> {
    // For a trait method the first generic type argument is `Self`.
    let Some(self_ty) = generics.types().next() else {
        return Ok(None);
    };
    let Some(kind) = spec_int_kind(tcx, self_ty) else {
        return Ok(None);
    };
    let sort = kind.sort();
    let method = tcx.item_name(def_id).to_string();

    let compare_op = match method.as_str() {
        "lt" => Some(CompareOp::Lt),
        "le" => Some(CompareOp::Le),
        "gt" => Some(CompareOp::Gt),
        "ge" => Some(CompareOp::Ge),
        "eq" => Some(CompareOp::Eq),
        "ne" => Some(CompareOp::Ne),
        _ => None,
    };
    if let Some(op) = compare_op {
        let [lhs, rhs] = two_args(args, &method)?;
        return Ok(Some(TrustVcExpr::Compare {
            op,
            left: Box::new(lower_spec_int_operand(tcx, thir, lhs, sort.clone())?),
            right: Box::new(lower_spec_int_operand(tcx, thir, rhs, sort)?),
        }));
    }

    let arith_op = match method.as_str() {
        "add" => Some(ArithOp::Add),
        "sub" => Some(ArithOp::Sub),
        "mul" => Some(ArithOp::Mul),
        _ => None,
    };
    if let Some(op) = arith_op {
        let [lhs, rhs] = two_args(args, &method)?;
        return Ok(Some(TrustVcExpr::Arith {
            op,
            left: Box::new(lower_spec_int_operand(tcx, thir, lhs, sort.clone())?),
            right: Box::new(lower_spec_int_operand(tcx, thir, rhs, sort.clone())?),
            ty: sort,
        }));
    }

    // div / rem / shifts / bit-ops / neg on spec int: not in the Slice-2 fragment
    // (spec div/mod-by-zero is unspecified). Fail closed rather than approximate.
    Err(DriverError::UnsupportedContract(format!(
        "spec-int operator `{method}` out of scalar quantifier fragment"
    )))
}

/// Extracts exactly the two operands of a binary operator method, failing closed
/// otherwise (an operator with the wrong arity is not in the fragment).
fn two_args(args: &[ExprId], method: &str) -> Result<[ExprId; 2], DriverError> {
    match args {
        [a, b] => Ok([*a, *b]),
        _ => Err(DriverError::UnsupportedContract(format!(
            "spec-int operator `{method}` did not take two operands"
        ))),
    }
}

/// Lowers an operand of a recognized spec-int operator into a math-integer
/// [`TrustVcExpr`] at `sort`. Peels the operator auto-reference (`&x`), then
/// accepts the spec-int bound var, an integer literal, or a nested spec-int
/// arithmetic call. Anything else (a captured fixed-width var, a non-int leaf)
/// fails closed so a mixed-sort body is never silently encoded.
fn lower_spec_int_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    id: ExprId,
    sort: TrustVcType,
) -> Result<TrustVcExpr, DriverError> {
    let id = peel_operand(thir, id);
    let expr = &thir[id];
    match &expr.kind {
        ExprKind::VarRef { id: var_id } => {
            // Only the spec-int bound var is allowed; a fixed-width captured var
            // would be a sort mismatch, so refuse it.
            let Some(var_kind) = spec_int_kind(tcx, expr.ty) else {
                return Err(DriverError::UnsupportedContract(
                    "non-spec-int variable in spec-int operand (sort mismatch)".into(),
                ));
            };
            Ok(TrustVcExpr::Var {
                name: tcx.hir_name(var_id.0).to_string(),
                ty: var_kind.sort(),
            })
        }
        ExprKind::Literal { lit, neg } => match &lit.node {
            LitKind::Int(value, _) => {
                let v = value.0 as i128;
                Ok(TrustVcExpr::IntLit {
                    value: if *neg { -v } else { v },
                    ty: sort,
                })
            }
            other => Err(DriverError::UnsupportedContract(format!(
                "spec-int operand literal {other:?} out of fragment"
            ))),
        },
        ExprKind::Call { fun, args, .. } => {
            if let ty::FnDef(def_id, generics) = thir[*fun].ty.kind() {
                if let Some(e) = try_lower_spec_int_op(tcx, thir, *def_id, generics, args)? {
                    return Ok(e);
                }
            }
            Err(DriverError::UnsupportedContract(
                "spec-int operand call out of fragment".into(),
            ))
        }
        _ => Err(DriverError::UnsupportedContract(
            "spec-int operand out of fragment".into(),
        )),
    }
}

/// Like [`peel`], but additionally strips the shared auto-reference (`Borrow`)
/// inserted around operator-method operands (`a < b` ⇒ `lt(&a, &b)`). Restricted
/// to operand position, where the borrow is a desugaring artifact with no
/// semantic effect; the general [`peel`] never strips references.
fn peel_operand(thir: &Thir<'_>, id: ExprId) -> ExprId {
    let mut id = peel(thir, id);
    loop {
        match &thir[id].kind {
            ExprKind::Borrow { arg, .. } => id = peel(thir, *arg),
            _ => return id,
        }
    }
}

// ===========================================================================
// Slice 3a: scalar structs.
//
// A NON-RECURSIVE, NON-GENERIC, NAMED-FIELD struct whose every field is scalar
// maps to a single-variant `TrustVcType::Datatype` — exactly the shape the syn
// front end produces (`StructDef::to_datatype_type`) and that the encoder
// registers natively (`register_datatype`/`try_declare_datatype`), so the
// constructor/selector roundtrip is a native datatype-theory invariant.
//
// The constructor/selector FnCall symbol names MUST match the encoder's scheme
// (`encoder::datatype::{variant_symbol_name, selector_symbol_name}`, which run
// `encoder::sanitize_symbol` on each component). Those helpers are `pub(crate)`
// to `trust-vc-core`, so we replicate the exact algorithm here. The struct
// oracle-diff gate (`tests/driver_oracle_diff.rs`) compiles the SAME struct
// contract through both this driver and the syn path and asserts verdict
// equality, so any drift between this replica and the encoder is caught.
// ===========================================================================

/// Replica of `trust_vc_core::encoder::sanitize_symbol` (a `pub(crate)` helper):
/// keep ASCII alphanumerics, collapse every run of other chars to a single `_`,
/// then trim leading/trailing `_`. For ordinary identifiers it is the identity.
fn sanitize_symbol(name: &str) -> String {
    let mut sanitized = String::with_capacity(name.len());
    let mut last_was_underscore = false;
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            sanitized.push(ch);
            last_was_underscore = false;
        } else if !last_was_underscore {
            sanitized.push('_');
            last_was_underscore = true;
        }
    }
    while sanitized.ends_with('_') {
        sanitized.pop();
    }
    while sanitized.starts_with('_') {
        sanitized.remove(0);
    }
    sanitized
}

/// Replica of `encoder::datatype::variant_symbol_name`: the constructor symbol
/// for a struct's sole variant.
fn variant_symbol_name(datatype_name: &str, variant_name: &str) -> String {
    format!(
        "{}_{}",
        sanitize_symbol(datatype_name),
        sanitize_symbol(variant_name)
    )
}

/// Replica of `encoder::datatype::selector_symbol_name` (+ its `selector_suffix`
/// empty-name fallback): the selector symbol for one field of a variant.
fn selector_symbol_name(datatype_name: &str, variant_name: &str, field_name: &str) -> String {
    let suffix = sanitize_symbol(field_name);
    let suffix = if suffix.is_empty() {
        "Datatype".to_string()
    } else {
        suffix
    };
    format!(
        "{}_{}",
        variant_symbol_name(datatype_name, variant_name),
        suffix
    )
}

// ===========================================================================
// Slice 3c: the OPAQUE TYPE-PARAMETER SORT (Verus-style parametric verification).
//
// A free type parameter `T` is verified ONCE over a fresh UNINTERPRETED sort —
// the encoder maps `TrustVcType::TypeParam(name)` to `Sort::Uninterpreted("Poly")`
// (a non-empty carrier with genuine EUF congruence: two independent `T` values
// are NOT forced equal, so the sort is never singleton-collapsed). A property
// proven over this free sort holds for EVERY concrete `T`, because any concrete
// type is a model of the free theory over an uninterpreted sort (see the
// congruence argument on `lower_spec_equality`).
//
// Only the operations that are SOUND in the free theory ever reach a `T` value:
// EUF equality (the `spec_eq`/`spec_ne` markers), field projection of a `T`
// field (selector), datatype construction with a `T` field (constructor), and
// passing `T` by value. Every STRUCTURE-assuming use — ordering, arithmetic, any
// trait-method call, `Clone`/`Copy`/`Default`, casts — surfaces as a THIR
// trait-method `Call` (or an unhandled node) and FAILS CLOSED through the strict
// whitelist. There is no oracle for the opaque sort (syn cannot resolve
// `ty::Param`), so this fail-closed boundary is the soundness firewall.
// ===========================================================================

/// Maps a free type parameter `ty::Param(p)` into the opaque sort
/// [`TrustVcType::TypeParam`], keyed by the parameter's source name (stable
/// within a function). Returns `None` for every non-parameter type so the caller
/// falls through to the scalar/datatype mappers or fails closed.
///
/// The name key is retained for diagnostics/round-tripping; the encoder erases
/// ALL type params to one shared `Sort::Uninterpreted("Poly")`. Sharing one sort
/// across distinct params (`A`, `B`) is CONSERVATIVE, never unsound: it only adds
/// models (an `A` value and a `B` value may share the domain), so a validity
/// (UNSAT-of-negation) result over the merged sort still implies validity for the
/// separate-sort (distinct concrete `A`/`B`) theory — it can only fail to prove,
/// never falsely prove. rustc's own type checker rejects any cross-param
/// operation (`a == b` for `a: A`, `b: B`) before THIR, so such a term never
/// reaches this lowering regardless.
fn map_opaque_type_param(ty: Ty<'_>) -> Option<TrustVcType> {
    if let ty::Param(param) = ty.kind() {
        return Some(TrustVcType::TypeParam(param.name.to_string()));
    }
    None
}

/// Maps a struct/enum FIELD type: a scalar/spec-int via [`map_binder_ty`], or a
/// free type parameter via [`map_opaque_type_param`] (the opaque sort). `None`
/// (fail closed) for any other non-scalar field — a nested/recursive datatype,
/// a reference, a collection, etc. — so no field constraint is silently dropped.
fn map_field_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TrustVcType> {
    map_binder_ty(tcx, ty).or_else(|| map_opaque_type_param(ty))
}

/// The datatype CARRIER name for an ADT instantiation. A non-generic ADT keeps
/// its bare item name (so the non-generic struct/enum oracle-diff parity with the
/// syn front end is preserved). A GENERIC instantiation appends a suffix derived
/// from its type arguments so distinct instantiations (`S<T>` vs `S<u32>`, `S<A>`
/// vs `S<B>`) NEVER collapse onto one carrier — a collision would let the encoder
/// conflate two datatypes whose fields have different sorts (a soundness hazard).
/// Fails closed (`None`) if any type argument is itself out of the modeled
/// fragment, so an unmodeled instantiation is refused rather than mis-named.
fn adt_carrier_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt: ty::AdtDef<'tcx>,
    args: GenericArgsRef<'tcx>,
) -> Option<String> {
    let base = tcx.item_name(adt.did()).to_string();
    let mut suffix_parts: Vec<String> = Vec::new();
    for arg_ty in args.types() {
        // Each type argument must itself be a modeled leaf sort (scalar, spec-int,
        // or opaque param). A nested-datatype type argument can never be a modeled
        // FIELD (fields go through `map_field_ty`, which refuses nested datatypes),
        // so failing closed here is conservative and sidesteps any recursion.
        let mapped = map_field_ty(tcx, arg_ty)?;
        suffix_parts.push(mapped.to_type_string());
    }
    if suffix_parts.is_empty() {
        Some(base)
    } else {
        Some(format!("{base}_{}", suffix_parts.join("_")))
    }
}

/// Maps a **named-field struct** ADT into a single-variant
/// [`TrustVcType::Datatype`], or `None` (fail closed) for anything outside it.
///
/// Accepted **only** when the type is a struct (not an enum/union), is NOT a
/// tuple/unit struct (those carry a `ctor`), has NO type/const generics
/// (monomorphic-first), has at least one field, and **every** field is scalar
/// (`bool`/`i*`/`u*`/`int`/`nat` via [`map_binder_ty`]). A non-scalar field
/// (another struct — including a recursive self-reference — or any non-scalar
/// type) makes [`map_binder_ty`] return `None`, which fails the whole struct
/// closed: recursive and nested structs are refused for free, so no field
/// constraint is ever silently dropped. The spec math-integers `int`/`nat` are
/// handled as `MathInt`/`Nat` in operand positions, never as data structs.
fn map_struct_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TrustVcType> {
    let ty::Adt(adt, args) = ty.kind() else {
        return None;
    };
    if !adt.is_struct() {
        return None; // enum / union → fail closed
    }
    if spec_int_kind(tcx, ty).is_some() {
        return None; // the `int`/`nat` spec shims are not data structs
    }
    // TYPE generics are now allowed: a `T`-typed field maps to the opaque sort via
    // `map_field_ty` (Slice 3c). CONST generics stay refused — a const parameter
    // is a value (monomorphization), not a sort, and is out of fragment.
    let counts = tcx.generics_of(adt.did()).own_counts();
    if counts.consts > 0 {
        return None;
    }
    let variant = adt.non_enum_variant();
    if variant.ctor.is_some() {
        return None; // tuple/unit struct (has a constructor) → fail closed
    }
    if variant.fields.is_empty() {
        return None; // field-less struct: outside the bounded scalar fragment
    }
    let mut fields: Vec<(String, TrustVcType)> = Vec::with_capacity(variant.fields.len());
    // Iterate in `FieldIdx` (declaration) order so field position i equals the
    // `ExprKind::Field { name: FieldIdx }` / constructor-domain index.
    for field in variant.fields.iter() {
        // `FieldDef::ty` substitutes `args` without normalizing. The mapper
        // accepts only scalars and bare type parameters, which need no
        // normalization, and rejects anything else.
        let field_ty = field.ty(tcx, args).skip_normalization();
        // Scalar/spec-int OR a free type parameter (opaque sort); non-scalar
        // (incl. nested/recursive datatype) → None → fail closed.
        let mapped = map_field_ty(tcx, field_ty)?;
        fields.push((field.name.to_string(), mapped));
    }
    // The sole variant keeps the real struct NAME (used verbatim in
    // constructor/selector symbols); the CARRIER name carries the generic-args
    // suffix so distinct instantiations stay distinct datatypes.
    let variant_name = tcx.item_name(adt.did()).to_string();
    let carrier = adt_carrier_name(tcx, *adt, args)?;
    Some(TrustVcType::Datatype {
        name: carrier,
        variants: vec![DatatypeVariant::new(variant_name, fields)],
    })
}

/// Maps a **non-recursive, non-generic enum** ADT into a multi-variant
/// [`TrustVcType::Datatype`] over the Slice-3b fragment, or `None` (fail closed)
/// for anything outside it.
///
/// Accepted **only** when the type is an enum with at least one variant, has NO
/// type/const generics (monomorphic-first), and **every field of every variant**
/// is scalar (`bool`/`i*`/`u*`/`int`/`nat` via [`map_binder_ty`]). Each variant
/// may be unit (no fields) or carry scalar fields (tuple fields are named by
/// their positional index `"0"`, `"1"`, … exactly as the syn front end's
/// builtins register them). A non-scalar field — another struct/enum, a
/// recursive self-reference, or a `Box<Self>` — makes [`map_binder_ty`] return
/// `None`, which fails the **whole** enum closed: recursion, generics, and
/// nested datatypes are refused for free, so no variant or field is ever
/// silently dropped and no phantom variant is invented. Variants are built in
/// `VariantIdx` (declaration) order, so `variants[i]` matches the THIR
/// `variant_index`.
fn map_enum_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TrustVcType> {
    let ty::Adt(adt, args) = ty.kind() else {
        return None;
    };
    if !adt.is_enum() {
        return None;
    }
    // TYPE generics are now allowed (a `T`-typed variant field maps to the opaque
    // sort via `map_field_ty`, Slice 3c); CONST generics stay refused.
    let counts = tcx.generics_of(adt.did()).own_counts();
    if counts.consts > 0 {
        return None;
    }
    if adt.variants().is_empty() {
        return None; // uninhabited enum: nothing to construct or match
    }
    // Carrier name carries the generic-args suffix so distinct instantiations
    // (`Opt<T>` vs `Opt<u32>`) stay distinct datatypes; variant names stay the
    // real Rust names (matched verbatim in `lower_variant_pattern`).
    let dt_name = adt_carrier_name(tcx, *adt, args)?;
    let mut variants: Vec<DatatypeVariant> = Vec::with_capacity(adt.variants().len());
    for variant in adt.variants().iter() {
        let mut fields: Vec<(String, TrustVcType)> = Vec::with_capacity(variant.fields.len());
        for field in variant.fields.iter() {
            // Unnormalized for the same reason as in the struct case above.
            let field_ty = field.ty(tcx, args).skip_normalization();
            // Scalar/spec-int OR a free type parameter (opaque sort); non-scalar
            // (incl. nested/recursive datatype) → None → fail closed.
            let mapped = map_field_ty(tcx, field_ty)?;
            fields.push((field.name.to_string(), mapped));
        }
        variants.push(DatatypeVariant::new(variant.name.to_string(), fields));
    }
    Some(TrustVcType::Datatype {
        name: dt_name,
        variants,
    })
}

/// Maps a struct (Slice 3a, [`map_struct_ty`]) or enum (Slice 3b,
/// [`map_enum_ty`]) ADT into a [`TrustVcType::Datatype`]. Unions and everything
/// non-ADT fail closed (`None`).
fn map_adt_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TrustVcType> {
    let ty::Adt(adt, _) = ty.kind() else {
        return None;
    };
    if adt.is_struct() {
        map_struct_ty(tcx, ty)
    } else if adt.is_enum() {
        map_enum_ty(tcx, ty)
    } else {
        None // union → fail closed
    }
}

/// Maps a local/parameter/return/var-ref type: a scalar via [`map_ty`], a
/// scalar/generic struct or enum via [`map_adt_ty`], or a free type parameter via
/// [`map_opaque_type_param`] (the opaque sort, Slice 3c). `None` (fail closed)
/// otherwise.
fn map_local_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<TrustVcType> {
    map_ty(ty)
        .or_else(|| map_adt_ty(tcx, ty))
        .or_else(|| map_opaque_type_param(ty))
}

/// Lowers a field projection `s.f` ([`ExprKind::Field`]) into the encoder
/// datatype **selector** `FnCall`. Fails closed when the receiver is not a
/// Slice-3a scalar struct (e.g. an enum, a tuple/generic/recursive struct, or a
/// reference) so a field read off an unmodeled value is never fabricated.
fn lower_field_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    id: ExprId,
) -> Result<TrustVcExpr, DriverError> {
    let ExprKind::Field { lhs, name, .. } = &thir[id].kind else {
        return Err(DriverError::UnsupportedContract(
            "internal: field-access lowering on non-Field node".into(),
        ));
    };
    let receiver_ty = thir[*lhs].ty;
    let struct_ty = map_struct_ty(tcx, receiver_ty).ok_or_else(|| {
        DriverError::UnsupportedContract(format!(
            "field access on out-of-fragment receiver type {receiver_ty:?}"
        ))
    })?;
    let TrustVcType::Datatype {
        name: dt_name,
        variants,
    } = &struct_ty
    else {
        return Err(DriverError::UnsupportedContract(
            "internal: scalar-struct type is not a single-variant datatype".into(),
        ));
    };
    let [variant] = variants.as_slice() else {
        return Err(DriverError::UnsupportedContract(
            "internal: scalar struct must be single-variant".into(),
        ));
    };
    // `map_struct_ty` built `variant.fields` in `FieldIdx` order, so the THIR
    // field index selects the matching `(name, ty)` directly.
    let idx = name.as_usize();
    let (field_name, field_ty) = variant.fields.get(idx).ok_or_else(|| {
        DriverError::UnsupportedContract(format!(
            "field index {idx} out of range for struct `{dt_name}`"
        ))
    })?;
    let receiver = lower_thir_expr(tcx, thir, *lhs)?;
    Ok(TrustVcExpr::FnCall {
        name: selector_symbol_name(dt_name, &variant.name, field_name),
        args: vec![receiver],
        return_ty: field_ty.clone(),
    })
}

/// Lowers a struct / enum-variant construction ([`ExprKind::Adt`]) into the
/// encoder datatype **constructor** `FnCall`, with arguments reordered into the
/// declared field order (= the constructor's domain order). The `variant_index`
/// selects the constructed variant (always `0` for a struct; the source variant
/// for an enum, e.g. `E::B(a)` or the unit `E::A`). Fails closed for
/// out-of-fragment datatypes (tuple/unit struct, union, generic/recursive/
/// non-scalar) and for `..base`/`..` (default-fields) updates, so no field is
/// dropped or defaulted to an unmodeled value and no phantom variant is built.
fn lower_adt_construct<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    ty: Ty<'tcx>,
    adt_expr: &thir::AdtExpr<'tcx>,
) -> Result<TrustVcExpr, DriverError> {
    if !matches!(adt_expr.base, AdtExprBase::None) {
        return Err(DriverError::UnsupportedContract(
            "struct/enum construction with `..base`/`..` default fields out of datatype fragment"
                .into(),
        ));
    }
    let adt_ty = map_adt_ty(tcx, ty).ok_or_else(|| {
        DriverError::UnsupportedContract(format!(
            "construction of out-of-fragment datatype {ty:?} (tuple/unit struct/union/generic/recursive/non-scalar)"
        ))
    })?;
    // Constructing a datatype with an OPAQUE (type-param) field is now SUPPORTED.
    // A `let s = S { f: x, .. }` emits the body relation `s == Ctor(x, ..)` — a
    // datatype-variable-equals-constructor assumption over an uninterpreted field
    // sort — which is sound + complete on ay >= the set-diff assumption fix
    // (ay 542e7f/25356919: dedup-robust array-axiom extraction; the earlier
    // drain-range panic that forced this path fail-closed is gone) atop main's
    // datatype-value-equality congruence (8deace993b) + constructor-injectivity
    // firewall (e3828748aa). The construct-then-project roundtrip Verifies for all
    // T (selector-of-constructor is a datatype axiom, sound over any sort).
    let TrustVcType::Datatype {
        name: dt_name,
        variants,
    } = &adt_ty
    else {
        return Err(DriverError::UnsupportedContract(
            "internal: datatype type is not a Datatype".into(),
        ));
    };
    // The THIR `variant_index` picks the constructed variant; `map_adt_ty` built
    // `variants` in `VariantIdx` order, so it indexes directly. (A struct is a
    // single variant at index 0.)
    let variant_index = adt_expr.variant_index.as_usize();
    let variant = variants.get(variant_index).ok_or_else(|| {
        DriverError::UnsupportedContract(format!(
            "variant index {variant_index} out of range for datatype `{dt_name}`"
        ))
    })?;
    if adt_expr.fields.len() != variant.fields.len() {
        // Every field must be explicitly provided (no `..base`, already refused);
        // a count mismatch means an unmodeled construction shape → fail closed.
        return Err(DriverError::UnsupportedContract(format!(
            "`{dt_name}::{}` construction provides {} of {} fields (no field may be dropped)",
            variant.name,
            adt_expr.fields.len(),
            variant.fields.len()
        )));
    }
    // Reorder the provided field expressions into declared field order, matching
    // the constructor's domain. Each declared field must be supplied exactly once.
    let mut args: Vec<TrustVcExpr> = Vec::with_capacity(variant.fields.len());
    for (i, _) in variant.fields.iter().enumerate() {
        let field_expr = adt_expr
            .fields
            .iter()
            .find(|fe| fe.name.as_usize() == i)
            .ok_or_else(|| {
                DriverError::UnsupportedContract(format!(
                    "`{dt_name}::{}` construction is missing field index {i}",
                    variant.name
                ))
            })?;
        args.push(lower_thir_expr(tcx, thir, field_expr.expr)?);
    }
    Ok(TrustVcExpr::FnCall {
        name: variant_symbol_name(dt_name, &variant.name),
        args,
        return_ty: adt_ty.clone(),
    })
}

/// Lowers a `match e { … }` ([`ExprKind::Match`]) on an **enum** scrutinee into a
/// [`TrustVcExpr::Match`] over the Slice-3b fragment (mirroring the syn front
/// end's `lower_match`), which the encoder lowers to an ite over per-variant
/// testers with payloads bound through the datatype selectors.
///
/// **Soundness (strict whitelist).** The fragment is deliberately narrow so a
/// mis-lowered or dropped arm can never become a too-strong VC:
/// * the scrutinee must be an in-fragment enum **value** ([`map_enum_ty`]); a
///   scalar, a reference, or an out-of-fragment ADT fails closed;
/// * every arm must be a **bare variant constructor pattern** (`E::A` / `E::B(x)`)
///   whose payload sub-patterns are all simple by-value binders — a guard, a
///   wildcard/default arm, an or-pattern, a literal or range sub-pattern, a
///   nested/`@`/`ref` binder, or a `..` rest fails the **whole** match closed;
/// * the arms must cover **exactly** the declared variants, once each (no missing
///   variant, no duplicate) — checked explicitly rather than trusting rustc, so a
///   non-exhaustive or over-covered match refuses rather than defaulting an arm.
///
/// Each arm's payload binder names come straight from the pattern, so the arm
/// body's `VarRef`s resolve to the encoder's selector-bound locals; no arm
/// condition is ever dropped and the enum is matched with exactly its own
/// variants (the oracle-diff catches any drift from the syn path).
fn lower_match<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    match_id: ExprId,
) -> Result<TrustVcExpr, DriverError> {
    let ExprKind::Match {
        scrutinee, arms, ..
    } = &thir[match_id].kind
    else {
        return Err(DriverError::UnsupportedContract(
            "internal: match lowering on non-Match node".into(),
        ));
    };
    let scrutinee_id = peel(thir, *scrutinee);
    let scrutinee_ty_raw = thir[scrutinee_id].ty;
    let scrutinee_ty = map_enum_ty(tcx, scrutinee_ty_raw).ok_or_else(|| {
        DriverError::UnsupportedContract(format!(
            "match scrutinee type {scrutinee_ty_raw:?} is not an in-fragment enum value"
        ))
    })?;
    let TrustVcType::Datatype { variants, .. } = &scrutinee_ty else {
        return Err(DriverError::UnsupportedContract(
            "internal: enum scrutinee type is not a Datatype".into(),
        ));
    };
    if arms.is_empty() {
        return Err(DriverError::UnsupportedContract(
            "match with zero arms out of scalar enum fragment".into(),
        ));
    }
    let scrutinee_expr = lower_thir_expr(tcx, thir, scrutinee_id)?;

    // Lower each arm; refuse guards / non-variant patterns / duplicate variants.
    let mut match_arms: Vec<MatchArm> = Vec::with_capacity(arms.len());
    let mut covered: Vec<String> = Vec::with_capacity(arms.len());
    for arm_id in arms.iter() {
        let arm = &thir[*arm_id];
        if arm.guard.is_some() {
            return Err(DriverError::UnsupportedContract(
                "match arm guard out of scalar enum fragment".into(),
            ));
        }
        let (variant_name, bindings) = lower_variant_pattern(&arm.pattern, &scrutinee_ty)?;
        if covered.contains(&variant_name) {
            return Err(DriverError::UnsupportedContract(format!(
                "match covers variant `{variant_name}` more than once (out of one-arm-per-variant fragment)"
            )));
        }
        covered.push(variant_name.clone());
        let body = lower_thir_expr(tcx, thir, arm.body)?;
        match_arms.push(MatchArm::new(
            MatchPattern::Constructor {
                variant_name,
                bindings,
                has_rest: false,
            },
            body,
        ));
    }
    // Exhaustiveness: exactly one arm per declared variant. `covered` has no
    // duplicates (checked) and each name is a real variant (checked in
    // `lower_variant_pattern`), so an equal count is a bijection onto the
    // variants — a complete cover with no wildcard/default arm.
    if covered.len() != variants.len() {
        return Err(DriverError::UnsupportedContract(format!(
            "non-exhaustive constructor match: covers {} of {} variants (one arm per variant \
             required; wildcard/default out of fragment)",
            covered.len(),
            variants.len()
        )));
    }

    // The match result type comes straight from the (already resolved) THIR node.
    let ty = map_local_ty(tcx, thir[match_id].ty).ok_or_else(|| {
        DriverError::UnsupportedType(format!("match result type {:?}", thir[match_id].ty))
    })?;
    Ok(TrustVcExpr::Match {
        scrutinee: Box::new(scrutinee_expr),
        arms: match_arms,
        ty,
    })
}

/// Lowers one match-arm pattern into `(variant_name, payload_binder_names)` for a
/// [`MatchPattern::Constructor`], or fails closed. Accepts **only** a bare
/// [`PatKind::Variant`] whose payload sub-patterns are all simple by-value
/// binders bound in declared field order; a `..` rest, an out-of-order/sparse
/// field set, a wildcard/nested/`@`/`ref` sub-pattern, or any non-variant
/// top-level pattern (wildcard, binding, literal, or, range, deref) refuses.
fn lower_variant_pattern(
    pat: &thir::Pat<'_>,
    scrutinee_ty: &TrustVcType,
) -> Result<(String, Vec<String>), DriverError> {
    let PatKind::Variant {
        adt_def,
        variant_index,
        subpatterns,
        ..
    } = &pat.kind
    else {
        return Err(DriverError::UnsupportedContract(
            "match arm pattern is not a bare enum variant (wildcard/binding/literal/or/range/deref \
             out of fragment)"
                .into(),
        ));
    };
    let variant_name = adt_def.variant(*variant_index).name.to_string();
    let TrustVcType::Datatype { variants, .. } = scrutinee_ty else {
        return Err(DriverError::UnsupportedContract(
            "internal: match scrutinee is not a Datatype".into(),
        ));
    };
    let dt_variant = variants
        .iter()
        .find(|v| v.name == variant_name)
        .ok_or_else(|| {
            DriverError::UnsupportedContract(format!(
                "match pattern variant `{variant_name}` is not a variant of the scrutinee datatype"
            ))
        })?;
    // Bind every field, in declared order, via a simple by-value binder. A
    // missing field (`..` rest) or a non-trivial sub-pattern fails closed so a
    // payload constraint is never dropped.
    let mut bindings: Vec<String> = Vec::with_capacity(dt_variant.fields.len());
    for (i, _) in dt_variant.fields.iter().enumerate() {
        let field_pat = subpatterns
            .iter()
            .find(|fp| fp.field.as_usize() == i)
            .ok_or_else(|| {
                DriverError::UnsupportedContract(format!(
                    "variant `{variant_name}` pattern does not bind field {i} (`..` rest out of fragment)"
                ))
            })?;
        // `simple_ident` accepts only a by-value binding with no sub-pattern
        // (`x`, `mut x`) — a `ref x`, `x @ P`, wildcard, or literal is refused.
        let name = field_pat.pattern.simple_ident().ok_or_else(|| {
            DriverError::UnsupportedContract(format!(
                "variant `{variant_name}` field {i} sub-pattern is not a simple by-value binder \
                 (nested/wildcard/`ref`/`@` out of fragment)"
            ))
        })?;
        bindings.push(name.to_string());
    }
    Ok((variant_name, bindings))
}

/// Maps a resolved rustc [`Ty`] into a [`TrustVcType`] for the supported scalar
/// set (integers and bool). Returns `None` for anything else so the caller fails
/// closed.
fn map_ty(ty: Ty<'_>) -> Option<TrustVcType> {
    match ty.kind() {
        ty::Bool => Some(TrustVcType::Bool),
        ty::Int(int_ty) => int_ty
            .bit_width()
            .map(|w| TrustVcType::Int { width: w as u32 })
            .or(Some(TrustVcType::Int { width: 64 })), // isize → target pointer width (default 64)
        ty::Uint(uint_ty) => uint_ty
            .bit_width()
            .map(|w| TrustVcType::Uint { width: w as u32 })
            .or(Some(TrustVcType::Uint { width: 64 })), // usize → target pointer width
        _ => None,
    }
}

/// Convenience entry point: run rustc as a verifying driver over `args`
/// (`["trust-vc-driver", "path/to/file.rs", ...]`) and return the collected
/// results. Mirrors how Verus's `rust_verify` wraps `RunCompiler`.
pub fn run(args: &[String]) -> Vec<DriverResult> {
    // Inject `-Zno-steal-thir` so the THIR survives to `after_analysis` (it is
    // otherwise stolen by `check_unsafety`). The Trust dev channel accepts it.
    let mut full_args = args.to_vec();
    if !full_args.iter().any(|a| a == NO_STEAL_THIR) {
        full_args.push(NO_STEAL_THIR.to_string());
    }
    // Turn on the contract macros' bare-marker surface bridge (alongside
    // `-Zno-steal-thir`). `--cfg trust_vc_driver` makes `requires!`/`ensures!`/
    // `forall!`/`exists!` expand to `__driver_markers::*` calls this driver reads.
    if !full_args
        .iter()
        .zip(full_args.iter().skip(1))
        .any(|(a, b)| a == "--cfg" && b == DRIVER_CFG)
    {
        full_args.push("--cfg".to_string());
        full_args.push(DRIVER_CFG.to_string());
    }
    let mut callbacks = TrustVcCallbacks::default();
    rustc_driver::run_compiler(&full_args, &mut callbacks);
    callbacks.results
}
