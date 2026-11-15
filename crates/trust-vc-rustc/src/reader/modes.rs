//! Verus's mode checker (`vir/src/modes.rs`), applied to the HIR the reader
//! reads.
//!
//! Verus checks modes after building VIR and checking well-formedness. Every
//! expression has a mode (exec, proof or spec), code runs in an outer mode,
//! and the check of a function stops at its first error. This module walks
//! one function's HIR in the order Verus walks the VIR built from it, and
//! applies the same rules with Verus's messages and spans:
//!
//! * spec operators and builtins (`==>`, `===`, `imply`, `spec_eq`,
//!   `equal`) produce spec values, which exec code cannot use;
//! * a function can only be called where its mode is allowed: exec functions
//!   from exec code, proof functions from ghost code outside spec code, spec
//!   functions from ghost code;
//! * ghost code cannot write exec variables, exec code cannot write or read
//!   ghost variables;
//! * clauses, assertions and spec function bodies are pure.
//!
//! The walk models the constructs the reader lowers, plus some that the
//! reader refuses only because they break a mode rule. Anything else stops
//! it with [`ModeCheck::Unknown`]: the function's modes are then not known.
//!
//! How the walk mirrors VIR (`rust_to_vir_expr.rs`): a local variable, a
//! field of anything and a dereference of a place are places, read through
//! `ReadPlace`; any other expression that a `let` binds, or that a field is
//! taken of, is a temporary place. A `*r` of a reference is `r` itself
//! (without `-V new-mut-ref`), with `r`'s span.
// quality-audit: allow-file allow-rust-size — one port of Verus's vir/src/modes.rs rule set, kept whole like its source

use std::collections::HashMap;

use rustc_ast::{BindingMode, ByRef};
use rustc_hir::def::{CtorKind, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir, HirId, PatKind};
use rustc_middle::ty::adjustment::{Adjust, DerefAdjustKind};
use rustc_middle::ty::{self, TyCtxt, TypeckResults};
use rustc_span::Span;

use trust_vc_vcir::Mode;

use super::attrs::{self, VerusAttr};
use super::{Cx, Refusal, UserError};
use crate::messages::{self, modes as msg, Phase};
use crate::verus_items::VerusItem;

mod variant_fields;

/// The result of checking one function's modes.
#[derive(Debug, Clone)]
pub(crate) enum ModeCheck {
    /// No mode error, with facts from the completed walk.
    Clean(CheckedModes),
    /// The first mode error, as Verus reports it.
    Error(UserError),
    /// The walk met something it does not model before any error.
    Unknown(Refusal),
}

/// Refusal tag for a function whose modes are not known.
pub(crate) const TAG_MODES_UNKNOWN: &str = "modes-unknown";

/// Native declaration facts needed by the shared mode walk. The product and
/// declaration producer supply their own actual indexes; this interface grants
/// no body, ownership or import authority to an index entry.
pub(super) trait ModeContext<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;
    fn function_mode(&self, def: DefId) -> Option<Mode>;
    fn body_owner(&self, def: LocalDefId) -> Option<LocalDefId>;
    fn declaration_attrs(&self, def: LocalDefId) -> attrs::ItemAttrs;
    fn verus_item(&self, def: DefId) -> Option<VerusItem>;
    fn constant_proxy(&self, def: LocalDefId) -> Option<LocalDefId>;
    /// Native-owned declaration semantics; no value/body authority is conveyed.
    fn constant_mode(&self, _def: LocalDefId) -> Option<trust_vc_vcir::ConstMode> {
        None
    }
    fn friendly_fn_path(&self, def: DefId) -> String;
    fn read_adt_field_modes(&self) -> bool;
    fn permits_adt_fields(&self, _definition: DefId) -> bool {
        self.read_adt_field_modes()
    }
    fn permits_variant_fields(&self, definition: DefId) -> bool {
        self.permits_adt_fields(definition)
    }
    /// The current native context's selected genuine field intrinsic. A
    /// diagnostic-item name alone cannot supply this identity. The original
    /// producer must join its actual CStore selection to its fresh builtin
    /// construction before a nominal-helper context can expose it.
    fn variant_field_intrinsic(&self) -> Option<DefId> {
        None
    }
    fn variant_test_intrinsic(&self) -> Option<DefId> {
        None
    }
    /// A separate, capability-owned call projection. It supplies no local
    /// body owner, parameter HIR ID or native ownership receipt.
    fn imported_call_modes(&self, _def: DefId) -> Option<CallModes> {
        None
    }
}

impl<'tcx> ModeContext<'tcx> for Cx<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn function_mode(&self, def: DefId) -> Option<Mode> {
        self.fns.get(&def).map(|info| info.mode)
    }

    fn body_owner(&self, def: LocalDefId) -> Option<LocalDefId> {
        // A trait declaration is checked through its actual specification
        // method, which owns the parameters and clauses.
        Some(self.spec_methods.get(&def).copied().unwrap_or(def))
    }

    fn declaration_attrs(&self, def: LocalDefId) -> attrs::ItemAttrs {
        Cx::declaration_attrs(self, def)
    }

    fn verus_item(&self, def: DefId) -> Option<VerusItem> {
        Cx::verus_item(self, def)
    }

    fn constant_proxy(&self, def: LocalDefId) -> Option<LocalDefId> {
        self.constants.proxy(def)
    }

    fn constant_mode(&self, def: LocalDefId) -> Option<trust_vc_vcir::ConstMode> {
        self.constants
            .declaration(def)
            .and_then(|d| self.constants.mode(d))
    }

    fn friendly_fn_path(&self, def: DefId) -> String {
        Cx::friendly_fn_path(self, def)
    }

    fn read_adt_field_modes(&self) -> bool {
        true
    }

    fn permits_adt_fields(&self, definition: DefId) -> bool {
        self.imported_nominal(definition).is_none()
    }

    fn variant_field_intrinsic(&self) -> Option<DefId> {
        self.local_variant_fields.as_ref()?.intrinsic(self.tcx)
    }
    fn variant_test_intrinsic(&self) -> Option<DefId> {
        self.local_variant_fields.as_ref()?.test_intrinsic(self.tcx)
    }

    fn permits_variant_fields(&self, definition: DefId) -> bool {
        self.local_variant_fields
            .as_ref()
            .is_some_and(|scope| scope.permits(self.tcx, definition))
            && self.adt_id(definition).is_some()
            && self.imported_nominal(definition).is_none()
    }

    fn imported_call_modes(&self, definition: DefId) -> Option<CallModes> {
        self.imports.as_ref()?.call_modes(self.tcx, definition)
    }
}

/// Check the modes of the Verus function `def_id`.
pub(crate) fn check_fn(cx: &Cx<'_>, def_id: LocalDefId) -> ModeCheck {
    check_with_context(cx, def_id)
}

pub(super) fn check_with_context<'tcx>(
    cx: &dyn ModeContext<'tcx>,
    def_id: LocalDefId,
) -> ModeCheck {
    let tcx = cx.tcx();
    let Some(owner) = cx.body_owner(def_id) else {
        return ModeCheck::Unknown(Refusal::new(
            TAG_MODES_UNKNOWN,
            "the declaration origin has no supported body-mode owner",
            tcx.def_span(def_id),
        ));
    };
    if matches!(
        tcx.hir_node_by_def_id(def_id),
        hir::Node::TraitItem(hir::TraitItem {
            kind: hir::TraitItemKind::Const(_, None),
            ..
        })
    ) && cx.constant_mode(def_id) == Some(trust_vc_vcir::ConstMode::Dual)
        && tcx.def_kind(def_id) == DefKind::AssocConst
        && tcx.def_kind(tcx.local_parent(def_id)) == DefKind::Trait
    {
        return match elaborate_signature_modes(cx, def_id.to_def_id(), tcx.def_span(def_id)) {
            Ok(signature) => ModeCheck::Clean(CheckedModes {
                signature,
                local_declarations: HashMap::new(),
            }),
            Err(problem) => ModeCheck::Unknown(problem),
        };
    }
    if tcx.hir_maybe_body_owned_by(owner).is_none() {
        return ModeCheck::Unknown(Refusal::new(
            TAG_MODES_UNKNOWN,
            "a function without a body",
            tcx.def_span(def_id),
        ));
    }
    let mut checker = Checker::new(cx, def_id, owner);
    match checker.function() {
        Ok(()) => match checker.signature {
            Some(signature) => ModeCheck::Clean(CheckedModes {
                signature,
                local_declarations: checker.local_declarations,
            }),
            None => ModeCheck::Unknown(Refusal::new(
                TAG_MODES_UNKNOWN,
                "a completed mode walk without signature facts",
                tcx.def_span(def_id),
            )),
        },
        Err(Stop::Error(error)) => ModeCheck::Error(error),
        Err(Stop::Unknown(refusal)) => ModeCheck::Unknown(refusal),
    }
}

/// A shared borrow or a dereference of a reference, which VIR keeps
/// transparent.
fn is_transparent_adjustment(a: &rustc_middle::ty::adjustment::Adjustment<'_>) -> bool {
    use rustc_middle::ty::adjustment::{AutoBorrow, AutoBorrowMutability};
    matches!(
        a.kind,
        Adjust::Deref(DerefAdjustKind::Builtin)
            | Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Not))
    )
}

/// `Exec <= Proof <= Spec` (`mode_le`).
fn le(a: Mode, b: Mode) -> bool {
    rank(a) <= rank(b)
}

/// The least upper bound (`mode_join`).
fn join(a: Mode, b: Mode) -> Mode {
    if rank(a) >= rank(b) {
        a
    } else {
        b
    }
}

/// The greatest lower bound (`mode_meet`).
fn meet(a: Mode, b: Mode) -> Mode {
    if rank(a) <= rank(b) {
        a
    } else {
        b
    }
}

fn rank(mode: Mode) -> u8 {
    match mode {
        Mode::Exec => 0,
        Mode::Proof => 1,
        Mode::Spec => 2,
    }
}

/// Whether code is inside a ghost block (Verus's `Ghost`): exec code is
/// outside every ghost block of an exec function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ghostness {
    Exec,
    Ghost,
}

/// Why the walk stopped.
enum Stop {
    Error(UserError),
    Unknown(Refusal),
}

type M<T> = Result<T, Stop>;

/// The mode of a variable, or a `let` whose mode the first assignment
/// decides (`#[verus::internal(infer_mode)]`, from `let tracked x = ..`).
#[derive(Debug, Clone, Copy)]
enum VarMode {
    Infer,
    Mode(Mode),
}

/// Why a signature declaration has its resolved mode.
#[derive(Debug, Clone, Copy)]
pub(crate) enum ModeOrigin {
    /// No mode attribute: `get_var_mode` of the function's mode.
    FunctionDefault,
    /// The first mode attribute on a parameter, or the last return-mode
    /// attribute on a function with a written return type.
    Attribute(Span),
    /// A function without a written return type returns in its own mode.
    ImplicitReturn,
}

/// A resolved signature mode, retaining the declaration that decided it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ResolvedMode {
    pub(crate) mode: Mode,
    pub(crate) origin: ModeOrigin,
}

impl ResolvedMode {
    /// The explicit declaration that supplied a mode, or the source span
    /// of the declaration whose default was used.
    pub(crate) fn declaration_span(self, fallback: Span) -> Span {
        match self.origin {
            ModeOrigin::Attribute(span) => span,
            ModeOrigin::FunctionDefault | ModeOrigin::ImplicitReturn => fallback,
        }
    }
}

/// Mode facts for one parameter, indexed in the signature's source order.
#[derive(Debug, Clone)]
pub(crate) struct ParameterModes {
    /// The parameter node, whose mode attributes were read. This is not
    /// the HIR id of its binding pattern.
    pub(crate) hir_id: HirId,
    pub(crate) span: Span,
    pub(crate) declared: ResolvedMode,
    pub(crate) mutable_reference: bool,
}

/// Shared elaboration of a function's signature. These facts do not imply
/// that the body passed mode checking or that tracked ownership was checked.
#[derive(Debug, Clone)]
pub(crate) struct SignatureModes {
    pub(crate) def_id: DefId,
    /// A trait declaration's specification method supplies its signature.
    pub(crate) body_owner: LocalDefId,
    /// The function mode already resolved by the crate reader.
    pub(crate) mode: Mode,
    pub(crate) params: Vec<ParameterModes>,
    pub(crate) ret: ResolvedMode,
}

/// Exactly the mode facts a call consumes. Foreign declarations must never
/// fabricate the local declaration/body IDs required by SignatureModes.
#[derive(Clone, Debug)]
pub(super) struct CallModes {
    pub(super) mode: Mode,
    pub(super) params: Vec<CallParameter>,
    pub(super) ret: Mode,
}

#[derive(Clone, Debug)]
pub(super) struct CallParameter {
    pub(super) mode: Mode,
    pub(super) mutable_reference: bool,
}

fn call_modes_with_context<'tcx>(
    cx: &dyn ModeContext<'tcx>,
    def: DefId,
    span: Span,
) -> Result<CallModes, Refusal> {
    if let Some(imported) = cx.imported_call_modes(def) {
        if def.is_local()
            || imported.mode != Mode::Spec
            || imported.ret != Mode::Spec
            || cx.function_mode(def) != Some(Mode::Spec)
            || imported
                .params
                .iter()
                .any(|parameter| parameter.mode != Mode::Spec || parameter.mutable_reference)
        {
            return Err(Refusal::new(
                TAG_MODES_UNKNOWN,
                "the foreign call projection is outside the licensed specification-only fragment",
                span,
            ));
        }
        return Ok(imported);
    }
    match signature_modes_with_context(cx, def, span) {
        SignatureModeResult::Known(signature) => Ok(CallModes {
            mode: signature.mode,
            params: signature
                .params
                .iter()
                .map(|parameter| CallParameter {
                    mode: parameter.declared.mode,
                    mutable_reference: parameter.mutable_reference,
                })
                .collect(),
            ret: signature.ret.mode,
        }),
        SignatureModeResult::Unknown(problem) => Err(problem),
    }
}

pub(super) fn call_return_mode(cx: &Cx<'_>, def: DefId, span: Span) -> Option<Mode> {
    call_modes_with_context(cx, def, span)
        .ok()
        .map(|modes| modes.ret)
}

/// A plain local declaration checked in its original function body.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CheckedLocal {
    /// The binding pattern, distinct from the declaration's HIR id.
    pub(crate) binding: HirId,
    /// The first explicit mode attribute, or the function's local default.
    pub(crate) declared: ResolvedMode,
    /// The binding's mode after ghost and pure-context rules.
    pub(crate) effective: Mode,
}

/// Authoritative mode facts available only after the whole walk succeeds.
#[derive(Debug, Clone)]
pub(crate) struct CheckedModes {
    pub(crate) signature: SignatureModes,
    /// Initialized and uninitialized plain declarations, excluding inference.
    pub(crate) local_declarations: HashMap<HirId, CheckedLocal>,
}

/// Whether the reader can elaborate every declaration of the signature.
#[derive(Debug, Clone)]
pub(crate) enum SignatureModeResult {
    Known(SignatureModes),
    Unknown(Refusal),
}

/// The signature modes used by the mode checker, body lowering and
/// ownership erasure. Unknown declarations retain the checker's refusal;
/// no mode, trait-implementation or ownership rule is bypassed here.
pub(crate) fn signature_modes(cx: &Cx<'_>, def_id: DefId, span: Span) -> SignatureModeResult {
    signature_modes_with_context(cx, def_id, span)
}

fn signature_modes_with_context<'tcx>(
    cx: &dyn ModeContext<'tcx>,
    def_id: DefId,
    span: Span,
) -> SignatureModeResult {
    match elaborate_signature_modes(cx, def_id, span) {
        Ok(modes) => SignatureModeResult::Known(modes),
        Err(refusal) => SignatureModeResult::Unknown(refusal),
    }
}

fn elaborate_signature_modes<'tcx>(
    cx: &dyn ModeContext<'tcx>,
    def_id: DefId,
    span: Span,
) -> Result<SignatureModes, Refusal> {
    let unknown = |detail| Refusal::new(TAG_MODES_UNKNOWN, detail, span);
    let Some(function_mode) = cx.function_mode(def_id) else {
        return Err(unknown(
            "a function that is not a Verus function of this crate",
        ));
    };
    let Some(local) = def_id.as_local() else {
        return Err(unknown("a function of another crate"));
    };
    let owner = cx
        .body_owner(local)
        .ok_or_else(|| unknown("the declaration origin has no supported signature-mode owner"))?;
    let item_attrs = cx.declaration_attrs(owner);
    if cx.constant_mode(local) == Some(trust_vc_vcir::ConstMode::Dual) {
        if function_mode != Mode::Spec || !item_attrs.unsupported.is_empty() {
            return Err(unknown("an unsupported dual constant signature"));
        }
        return Ok(SignatureModes {
            def_id,
            body_owner: owner,
            mode: Mode::Spec,
            params: Vec::new(),
            ret: ResolvedMode {
                mode: Mode::Exec,
                origin: ModeOrigin::FunctionDefault,
            },
        });
    }
    local_signature_modes(cx.tcx(), local, owner, function_mode, &item_attrs, span)
}

/// Elaborate a local declaration using the same rules as the reader. This
/// supplies declaration modes only: callers separately establish source/macro
/// provenance, body mode correctness, ownership and import authority.
/// The product caller supplies its authoritative declaration attributes,
/// including the validated const/proxy filter. Observers supply their actual
/// raw declaration attributes, without borrowing that product authority.
pub(super) fn local_signature_modes(
    tcx: TyCtxt<'_>,
    local: LocalDefId,
    owner: LocalDefId,
    function_mode: Mode,
    item_attrs: &attrs::ItemAttrs,
    span: Span,
) -> Result<SignatureModes, Refusal> {
    let unknown = |detail| Refusal::new(TAG_MODES_UNKNOWN, detail, span);
    let hir_id = tcx.local_def_id_to_hir_id(owner);
    if !item_attrs.unsupported.is_empty() {
        return Err(unknown(
            "a function with attributes the reader does not read",
        ));
    }
    let Some(body) = tcx.hir_maybe_body_owned_by(owner) else {
        return Err(unknown("a function without a body"));
    };
    let default = default_var_mode(function_mode);
    let mut params = Vec::new();
    for param in body.params {
        let ty = tcx.typeck(owner).pat_ty(param.pat);
        params.push(ParameterModes {
            hir_id: param.hir_id,
            span: param.span,
            declared: declared_mode(tcx, param.hir_id, default, param.span)?,
            mutable_reference: matches!(ty.kind(), ty::Ref(_, _, m) if m.is_mut()),
        });
    }
    let written_return = tcx
        .hir_fn_decl_by_hir_id(hir_id)
        .is_some_and(|decl| matches!(decl.output, hir::FnRetTy::Return(_)));
    let mut ret = ResolvedMode {
        mode: if written_return {
            default
        } else {
            function_mode
        },
        origin: if written_return {
            ModeOrigin::FunctionDefault
        } else {
            ModeOrigin::ImplicitReturn
        },
    };
    if written_return {
        for (attr, at) in attrs::verus_attrs(tcx.hir_attrs(hir_id)) {
            if let VerusAttr::ReturnMode(mode) = attr {
                ret = ResolvedMode {
                    mode,
                    origin: ModeOrigin::Attribute(at),
                };
            }
        }
    }
    Ok(SignatureModes {
        def_id: local.to_def_id(),
        body_owner: owner,
        mode: function_mode,
        params,
        ret,
    })
}

fn default_var_mode(mode: Mode) -> Mode {
    if mode == Mode::Proof {
        Mode::Spec
    } else {
        mode
    }
}

/// The first mode attribute decides the mode; any unsupported attribute
/// still makes the declaration unknown, even after a mode was found.
fn declared_mode(
    tcx: TyCtxt<'_>,
    hir_id: HirId,
    default: Mode,
    span: Span,
) -> Result<ResolvedMode, Refusal> {
    let mut mode = None;
    for (attr, at) in attrs::verus_attrs(tcx.hir_attrs(hir_id)) {
        match attr {
            VerusAttr::Mode(value) => {
                mode.get_or_insert(ResolvedMode {
                    mode: value,
                    origin: ModeOrigin::Attribute(at),
                });
            }
            VerusAttr::VerusMacro => {}
            other => {
                return Err(Refusal::new(
                    TAG_MODES_UNKNOWN,
                    format!("{other:?} on a declaration"),
                    at.to(span),
                ));
            }
        }
    }
    Ok(mode.unwrap_or(ResolvedMode {
        mode: default,
        origin: ModeOrigin::FunctionDefault,
    }))
}

struct Checker<'a, 'tcx> {
    cx: &'a dyn ModeContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    def_id: LocalDefId,
    body_owner: LocalDefId,
    fun_mode: Mode,
    vars: HashMap<HirId, VarMode>,
    signature: Option<SignatureModes>,
    local_declarations: HashMap<HirId, CheckedLocal>,
    /// Clauses, assertions and spec function bodies: every read is spec and
    /// nothing may be assigned.
    in_pure: bool,
    block: Ghostness,
    /// The mode of the return value, when the function has one.
    ret_mode: Option<Mode>,
    /// Inside a `proof { .. }` block of spec code (`push_in_proof_in_spec`).
    in_proof_in_spec: bool,
    /// Inside the proof of an `assert .. by` (`push_in_forall_stmt`).
    in_assert_by: bool,
}

impl<'a, 'tcx> Checker<'a, 'tcx> {
    fn new(cx: &'a dyn ModeContext<'tcx>, def_id: LocalDefId, body_owner: LocalDefId) -> Self {
        let tcx = cx.tcx();
        let fun_mode = cx.function_mode(def_id.to_def_id()).unwrap_or(Mode::Exec);
        Self {
            cx,
            tcx,
            typeck: tcx.typeck(body_owner),
            def_id,
            body_owner,
            fun_mode,
            vars: HashMap::new(),
            signature: None,
            local_declarations: HashMap::new(),
            in_pure: false,
            block: Ghostness::Exec,
            ret_mode: None,
            in_proof_in_spec: false,
            in_assert_by: false,
        }
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    fn error<T>(&self, span: Span, message: impl Into<String>) -> M<T> {
        Err(Stop::Error(UserError::new(Phase::Modes, span, message)))
    }

    fn unknown<T>(&self, detail: impl Into<String>, span: Span) -> M<T> {
        Err(Stop::Unknown(Refusal::new(TAG_MODES_UNKNOWN, detail, span)))
    }

    /// The type of `e` as Verus sees it (after adjustments) is `()`.
    fn is_unit(&self, e: &hir::Expr<'_>) -> bool {
        self.typeck.expr_ty_adjusted(e).is_unit()
    }

    /// The expected mode of an expression statement or an `if` condition:
    /// exec outside ghost blocks, spec inside them.
    fn stmt_expect(&self) -> Mode {
        match self.block {
            Ghostness::Exec => Mode::Exec,
            Ghostness::Ghost => Mode::Spec,
        }
    }

    /// Verus's default mode of a variable of a function of mode `mode`
    /// (`attributes.rs`, `get_var_mode`): proof functions have spec
    /// variables unless marked.
    fn default_var_mode(mode: Mode) -> Mode {
        default_var_mode(mode)
    }

    fn var_mode(&self, hir_id: HirId, span: Span) -> M<Mode> {
        match self.vars.get(&hir_id) {
            Some(VarMode::Mode(mode)) => Ok(*mode),
            Some(VarMode::Infer) => {
                self.unknown("a read of a variable whose mode is not decided yet", span)
            }
            None => self.unknown("a variable declared outside the function", span),
        }
    }

    /// The callee a call's function expression resolves to.
    fn callee(&self, func: &hir::Expr<'_>) -> Option<DefId> {
        let hir::ExprKind::Path(qpath) = &func.kind else {
            return None;
        };
        match self.typeck.qpath_res(qpath, func.hir_id) {
            Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => Some(def_id),
            _ => None,
        }
    }

    /// The mode a field of a struct is declared with; exec by default.
    fn field_mode(&self, e: &hir::Expr<'_>, base: &hir::Expr<'_>) -> M<Mode> {
        match self.typeck.expr_ty_adjusted(base).kind() {
            ty::Tuple(_) => Ok(Mode::Exec),
            ty::Adt(adt, _) if adt.is_struct() => {
                if !self.cx.permits_adt_fields(adt.did()) {
                    return self.unknown(
                        "ADT field mode reads are outside this producer slice",
                        e.span,
                    );
                }
                let index = self.typeck.field_index(e.hir_id);
                let field = &adt.non_enum_variant().fields[index];
                let Some(local) = field.did.as_local() else {
                    return self.unknown("a field of a struct of another crate", e.span);
                };
                self.declared_mode(self.tcx.local_def_id_to_hir_id(local), Mode::Exec, e.span)
            }
            _ => self.unknown("a field of something that is not a struct or tuple", e.span),
        }
    }

    /// The mode a datatype is declared with (`ghost struct` is spec, `tracked
    /// struct` proof); exec by default.
    fn datatype_mode(&self, adt: ty::AdtDef<'tcx>, span: Span) -> M<Mode> {
        let Some(local) = adt.did().as_local() else {
            return self.unknown("a struct of another crate", span);
        };
        if !adt.is_struct() && !adt.is_enum() {
            return self.unknown("a union value", span);
        }
        self.declared_mode(self.tcx.local_def_id_to_hir_id(local), Mode::Exec, span)
    }

    /// The first mode attribute on a declaration (`get_mode`), or
    /// `default`. Any other Verus attribute makes the declaration unknown.
    fn declared_mode(&self, hir_id: HirId, default: Mode, span: Span) -> M<Mode> {
        declared_mode(self.tcx, hir_id, default, span)
            .map(|resolved| resolved.mode)
            .map_err(Stop::Unknown)
    }

    /// The modes of the signature of a Verus function of this crate
    /// (`rust_to_vir_func.rs`): parameters are `get_var_mode` of the
    /// function's mode unless marked, the return value likewise, and a
    /// function without a written return type returns in its own mode.
    fn sig_modes(&self, def_id: DefId, span: Span) -> M<SignatureModes> {
        match signature_modes_with_context(self.cx, def_id, span) {
            SignatureModeResult::Known(modes) => Ok(modes),
            SignatureModeResult::Unknown(refusal) => Err(Stop::Unknown(refusal)),
        }
    }

    // ------------------------------------------------------------------
    // The function (`check_function`)
    // ------------------------------------------------------------------

    fn function(&mut self) -> M<()> {
        let tcx = self.tcx;
        let def_id = self.def_id;
        let owner = self.body_owner;
        let hir_id = tcx.local_def_id_to_hir_id(def_id);
        let span = tcx.def_span(def_id);
        let item_attrs = attrs::item_attrs(tcx.hir_attrs(hir_id));
        let sig = self.sig_modes(def_id.to_def_id(), span)?;
        self.signature = Some(sig.clone());
        let Some(body) = tcx.hir_maybe_body_owned_by(owner) else {
            return self.unknown("a function without a body", span);
        };
        self.trait_impl_modes(&sig, body.params)?;
        if self.cx.constant_mode(def_id) == Some(trust_vc_vcir::ConstMode::Dual) {
            if !body.params.is_empty() {
                return self.unknown("a constant initializer with parameters", span);
            }
            self.fun_mode = Mode::Exec;
            self.block = Ghostness::Exec;
            self.in_pure = false;
            self.ret_mode = Some(Mode::Exec);
            if item_attrs.external_body {
                return Ok(());
            }
            return self.has_mode(body.value, Mode::Exec, Mode::Exec);
        }

        // Parameters.
        for (param, facts) in body.params.iter().zip(&sig.params) {
            let mode = facts.declared.mode;
            let PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, ident, None) = param.pat.kind
            else {
                return self.unknown("a parameter that is not a plain name", param.pat.span);
            };
            if !le(self.fun_mode, mode) {
                // Verus names the parameter by its VIR variable, the name
                // and the binding's HIR local id (`x~2`).
                let name = format!("{}~{}", ident.name, pat_hir.local_id.as_usize());
                return self.error(span, msg::param_mode(&name, mode.name()));
            }
            self.vars.insert(pat_hir, VarMode::Mode(mode));
        }

        let hir::ExprKind::Block(block, None) = body.value.kind else {
            return self.unknown("a function body that is not a block", body.value.span);
        };

        // Header: `requires` and `recommends` (a spec function's
        // requirements), then `ensures`, whatever order they are written in.
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        // `decreases` measures and the `when` condition: pure spec code,
        // checked like `requires` (`check_function`).
        let mut measures: Vec<&'tcx hir::Expr<'tcx>> = Vec::new();
        let mut header_len = 0;
        for stmt in block.stmts {
            let hir::StmtKind::Semi(e) = stmt.kind else {
                break;
            };
            let hir::ExprKind::Call(func, args) = e.kind else {
                break;
            };
            let Some(callee) = self.callee(func) else {
                break;
            };
            let Some(item) = self.cx.verus_item(callee) else {
                break;
            };
            if !item.is_header() {
                break;
            }
            // Neither holds an expression.
            if matches!(item, VerusItem::OpensInvariantsNone | VerusItem::NoUnwind) {
                header_len += 1;
                continue;
            }
            let [arg] = args else {
                return self.unknown("a header call without one argument", e.span);
            };
            match item {
                VerusItem::Requires | VerusItem::Recommends => requires.push(arg),
                VerusItem::Ensures => ensures.push(arg),
                VerusItem::OtherHeader => match tcx.item_name(callee).as_str() {
                    "decreases" => match arg.kind {
                        hir::ExprKind::Tup(parts) => measures.extend(parts.iter()),
                        _ => measures.push(arg),
                    },
                    "decreases_when" => measures.push(arg),
                    // A path to the function, not an expression Verus
                    // checks.
                    "decreases_by" | "recommends_by" | "extra_dependency" => {}
                    _ => return self.unknown("a header the reader does not read", e.span),
                },
                _ => return self.unknown("a header the reader does not read", e.span),
            }
            header_len += 1;
        }
        for arg in requires {
            self.clause_list(arg, VerusItem::Requires)?;
        }
        for arg in ensures {
            match arg.kind {
                hir::ExprKind::Closure(closure) => {
                    let closure_body = tcx.hir_body(closure.body);
                    let [param] = closure_body.params else {
                        return self.unknown("an ensures closure without one parameter", arg.span);
                    };
                    let PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, _, None) =
                        param.pat.kind
                    else {
                        return self
                            .unknown("a return value that is not a plain name", param.pat.span);
                    };
                    self.vars.insert(pat_hir, VarMode::Mode(Mode::Spec));
                    self.clause_list(closure_body.value, VerusItem::Ensures)?;
                }
                _ => self.clause_list(arg, VerusItem::Ensures)?,
            }
        }

        for measure in measures {
            let saved = (self.block, self.in_pure);
            self.block = Ghostness::Ghost;
            self.in_pure = true;
            let checked = self.has_mode(measure, Mode::Spec, Mode::Spec);
            (self.block, self.in_pure) = saved;
            checked?;
        }

        let written_return = tcx
            .hir_fn_decl_by_hir_id(hir_id)
            .is_some_and(|decl| matches!(decl.output, hir::FnRetTy::Return(_)));
        if written_return {
            if !le(self.fun_mode, sig.ret.mode) {
                return self.error(span, msg::return_mode(sig.ret.mode.name()));
            }
            self.ret_mode = Some(sig.ret.mode);
        }

        // Verus drops the body of an `external_body` function, and of an
        // `uninterp` spec function (which `verus!` marks external_body). A
        // trait method declaration has none.
        if item_attrs.external_body || owner != def_id {
            return Ok(());
        }

        // The body, with the function's mode as outer mode and its return
        // mode as expected mode.
        self.block = if self.fun_mode == Mode::Exec {
            Ghostness::Exec
        } else {
            Ghostness::Ghost
        };
        self.in_pure = self.fun_mode == Mode::Spec;
        let mode = self.block_stmts(
            &block.stmts[header_len..],
            block.expr,
            self.fun_mode,
            sig.ret.mode,
        )?;
        if !self.is_unit(body.value) && !le(mode, sig.ret.mode) {
            return self.error(
                body.value.span,
                msg::expr_mode(mode.name(), sig.ret.mode.name()),
            );
        }
        Ok(())
    }

    /// `check_function`'s first rule for a method implementing a trait
    /// method: the method, each parameter and the return value have the
    /// declaration's modes. Errors are at the method's signature, a
    /// parameter's at the parameter.
    fn trait_impl_modes(&self, sig: &SignatureModes, params: &[hir::Param<'_>]) -> M<()> {
        let tcx = self.tcx;
        if tcx.trait_impl_of_assoc(self.def_id.to_def_id()).is_none() {
            return Ok(());
        }
        // A method of an implementation of another crate's trait is checked
        // against Verus's rules for those (`traits.rs`, `check_modes`) by the
        // reader.
        let Some(trait_fn) = tcx
            .associated_item(self.def_id)
            .trait_item_def_id()
            .filter(|d| d.is_local())
        else {
            return Ok(());
        };
        let sig_span = super::sig_span(tcx, self.def_id);
        let expected = self.sig_modes(trait_fn, sig_span)?;
        if sig.mode != expected.mode {
            return self.error(sig_span, messages::traits::impl_mode(expected.mode.name()));
        }
        if expected.params.len() != sig.params.len() || params.len() != sig.params.len() {
            return self.unknown("a trait method implemented with other parameters", sig_span);
        }
        for ((param, facts), expected) in params.iter().zip(&sig.params).zip(&expected.params) {
            if facts.declared.mode != expected.declared.mode {
                return self.error(
                    param.span,
                    messages::traits::impl_param_mode(expected.declared.mode.name()),
                );
            }
        }
        if sig.ret.mode != expected.ret.mode {
            return self.error(
                sig_span,
                messages::traits::impl_return_mode(expected.ret.mode.name()),
            );
        }
        Ok(())
    }

    /// The source clauses of a scalar or array header argument. Only ensures
    /// erases resolved diagnostic-item typing aids, at every position.
    fn clause_elements(
        &self,
        arr: &'tcx hir::Expr<'tcx>,
        header: VerusItem,
    ) -> Vec<&'tcx hir::Expr<'tcx>> {
        // One expression is a list of one (`extract_array`).
        let elems: Vec<&'tcx hir::Expr<'tcx>> = match arr.kind {
            hir::ExprKind::Array(elems) => elems.iter().collect(),
            _ => vec![arr],
        };
        elems
            .into_iter()
            .filter(|elem| {
                if header == VerusItem::Ensures {
                    if let hir::ExprKind::Call(func, _) = elem.kind {
                        if self.callee(func).and_then(|d| self.cx.verus_item(d))
                            == Some(VerusItem::ConstrainType)
                        {
                            return false;
                        }
                    }
                }
                true
            })
            .collect()
    }

    /// Check every retained clause as pure Spec code.
    fn clause_list(&mut self, arr: &'tcx hir::Expr<'tcx>, header: VerusItem) -> M<()> {
        let saved = (self.block, self.in_pure);
        self.block = Ghostness::Ghost;
        self.in_pure = true;
        for elem in self.clause_elements(arr, header) {
            self.has_mode(elem, Mode::Spec, Mode::Spec)?;
        }
        (self.block, self.in_pure) = saved;
        Ok(())
    }

    // ------------------------------------------------------------------
    // Statements (`check_stmt`)
    // ------------------------------------------------------------------

    /// A block's statements and tail; its mode is the tail's, or the outer
    /// mode without a tail.
    fn block_stmts(
        &mut self,
        stmts: &'tcx [hir::Stmt<'tcx>],
        tail: Option<&'tcx hir::Expr<'tcx>>,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        for stmt in stmts {
            self.stmt(stmt, outer)?;
        }
        match tail {
            Some(tail) => self.expr(tail, outer, expect),
            None => Ok(outer),
        }
    }

    fn stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>, outer: Mode) -> M<()> {
        match stmt.kind {
            hir::StmtKind::Let(local) => self.let_stmt(local, outer),
            hir::StmtKind::Semi(e) | hir::StmtKind::Expr(e) => {
                if self.is_dummy_capture(e) {
                    return Ok(());
                }
                let expect = self.stmt_expect();
                self.expr(e, outer, expect)?;
                Ok(())
            }
            hir::StmtKind::Item(_) => self.unknown("an item inside a function body", stmt.span),
        }
    }

    /// `dummy_capture_new()` / `dummy_capture_consume(..)`, which Verus
    /// skips (`is_ignorable_dummy_capture_operation`).
    fn is_dummy_capture(&self, e: &hir::Expr<'_>) -> bool {
        match e.kind {
            hir::ExprKind::Call(func, _) => matches!(
                self.callee(func).and_then(|d| self.cx.verus_item(d)),
                Some(VerusItem::DummyCaptureNew | VerusItem::DummyCaptureConsume)
            ),
            _ => false,
        }
    }

    /// `StmtX::Decl`.
    fn let_stmt(&mut self, local: &'tcx hir::LetStmt<'tcx>, outer: Mode) -> M<()> {
        if local.els.is_some() {
            return self.unknown("`let .. else`", local.span);
        }
        let mut declared = None;
        let mut infer = false;
        for (attr, attr_span) in attrs::verus_attrs(self.tcx.hir_attrs(local.hir_id)) {
            match attr {
                // The first mode attribute counts (`get_var_mode`).
                VerusAttr::Mode(mode) => {
                    declared.get_or_insert(ResolvedMode {
                        mode,
                        origin: ModeOrigin::Attribute(attr_span),
                    });
                }
                VerusAttr::InferMode => infer = true,
                // Only matter for warnings and prophecy, which the reader
                // does not read.
                VerusAttr::LetMarker(_) => {}
                other => return self.unknown(format!("{other:?} on a let"), attr_span),
            }
        }
        let pat_span = local.pat.span;
        if infer {
            // Only `let x;` is marked this way; its first assignment from a
            // variable decides its mode.
            let (PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, _, None), None) =
                (local.pat.kind, local.init)
            else {
                return self.unknown("an infer_mode let that is not `let x;`", pat_span);
            };
            self.vars.insert(pat_hir, VarMode::Infer);
            return Ok(());
        }
        let declared = declared.unwrap_or(ResolvedMode {
            mode: Self::default_var_mode(self.fun_mode),
            origin: ModeOrigin::FunctionDefault,
        });
        let mut mode = declared.mode;
        if self.block == Ghostness::Ghost && mode == Mode::Exec {
            mode = Mode::Spec;
        }
        if self.block == Ghostness::Exec && mode != Mode::Exec && local.init.is_some() {
            return self.error(pat_span, msg::EXEC_INITIALIZES_NON_EXEC);
        }
        if !le(outer, mode) {
            return self.error(pat_span, messages::pattern_mode(mode.name()));
        }
        if let Some(init) = local.init {
            self.place_has_mode(init, outer, mode)?;
        }
        let bound = if self.in_pure { Mode::Spec } else { mode };
        self.bind_let_pattern(local.pat, bound)?;
        if let PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) = local.pat.kind {
            self.local_declarations.insert(
                local.hir_id,
                CheckedLocal {
                    binding,
                    declared,
                    effective: bound,
                },
            );
        }
        Ok(())
    }

    /// Register value bindings only after checking the initializer's mode.
    /// Struct fields inherit their declared mode joined with the pattern's.
    fn bind_let_pattern(&mut self, pat: &'tcx hir::Pat<'tcx>, mode: Mode) -> M<()> {
        if self
            .typeck
            .pat_adjustments()
            .get(pat.hir_id)
            .is_some_and(|a| !a.is_empty())
        {
            return self.unknown("a value pattern with reference adjustments", pat.span);
        }
        match pat.kind {
            PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, _, None) => {
                if self
                    .typeck
                    .pat_binding_modes()
                    .get(pat_hir)
                    .is_some_and(|binding| matches!(binding, BindingMode(ByRef::Yes(..), _)))
                {
                    return self.unknown("a reference binding in a value pattern", pat.span);
                }
                self.vars.insert(pat_hir, VarMode::Mode(mode));
                Ok(())
            }
            PatKind::Tuple(elems, _) => {
                for elem in elems {
                    self.bind_let_pattern(elem, mode)?;
                }
                Ok(())
            }
            PatKind::Struct(_, fields, _) => {
                if !self.cx.read_adt_field_modes() {
                    return self.unknown(
                        "ADT pattern field modes are outside this producer slice",
                        pat.span,
                    );
                }
                let adt = self.pattern_struct(pat)?;
                for field in fields {
                    let Some(index) = self.typeck.opt_field_index(field.hir_id) else {
                        return self
                            .unknown("a pattern field without a compiler index", field.span);
                    };
                    let Some(decl) = adt.non_enum_variant().fields.get(index) else {
                        return self.unknown("a pattern field outside its type", field.span);
                    };
                    let field_mode = self.constructor_field_mode(decl, field.span)?;
                    self.bind_let_pattern(field.pat, join(mode, field_mode))?;
                }
                Ok(())
            }
            PatKind::TupleStruct(_, parts, rest) => {
                if !self.cx.read_adt_field_modes() {
                    return self.unknown(
                        "ADT pattern field modes are outside this producer slice",
                        pat.span,
                    );
                }
                let adt = self.pattern_struct(pat)?;
                let fields = &adt.non_enum_variant().fields;
                let Some(gap) = fields.len().checked_sub(parts.len()) else {
                    return self.unknown("a tuple struct pattern with too many fields", pat.span);
                };
                if rest.as_opt_usize().is_none() && gap != 0 {
                    return self.unknown("a tuple struct pattern with missing fields", pat.span);
                }
                for (position, part) in parts.iter().enumerate() {
                    let index = position
                        + if rest.as_opt_usize().is_some_and(|r| position >= r) {
                            gap
                        } else {
                            0
                        };
                    let Some(field) = fields.iter().nth(index) else {
                        return self
                            .unknown("a tuple struct pattern field outside its type", part.span);
                    };
                    let field_mode = self.constructor_field_mode(field, part.span)?;
                    self.bind_let_pattern(part, join(mode, field_mode))?;
                }
                Ok(())
            }
            PatKind::Wild => Ok(()),
            _ => self.unknown(
                "a let pattern outside plain values, tuples and local structs",
                pat.span,
            ),
        }
    }

    fn pattern_struct(&self, pat: &hir::Pat<'_>) -> M<ty::AdtDef<'tcx>> {
        let ty::Adt(adt, _) = self.typeck.pat_ty(pat).kind() else {
            return self.unknown("a struct pattern on a non-struct value", pat.span);
        };
        if !self.cx.permits_adt_fields(adt.did()) {
            return self.unknown(
                "ADT pattern field modes are outside this declaration capability",
                pat.span,
            );
        }
        if !adt.is_struct() {
            return self.unknown(
                "an enum or union value pattern is outside the current native slice",
                pat.span,
            );
        }
        self.datatype_mode(*adt, pat.span)?;
        Ok(*adt)
    }

    fn constructor_field_mode(&self, field: &ty::FieldDef, span: Span) -> M<Mode> {
        let Some(local) = field.did.as_local() else {
            return self.unknown("a field of a struct of another crate", span);
        };
        self.declared_mode(self.tcx.local_def_id_to_hir_id(local), Mode::Exec, span)
    }

    // ------------------------------------------------------------------
    // Places (`check_place`)
    // ------------------------------------------------------------------

    /// Is `e` a place in VIR: a local variable, a field, or a dereference of
    /// a place? Expressions with adjustments or Verus attributes are not.
    fn is_place(&self, e: &hir::Expr<'_>) -> bool {
        // A dereference of a reference keeps the place it adjusts.
        if !self
            .typeck
            .expr_adjustments(e)
            .iter()
            .all(|a| matches!(a.kind, Adjust::Deref(DerefAdjustKind::Builtin)))
        {
            return false;
        }
        self.is_place_unadjusted(e)
    }

    /// [`Self::is_place`] of `e` as written, its adjustments aside.
    fn is_place_unadjusted(&self, e: &hir::Expr<'_>) -> bool {
        if !attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id)).is_empty() {
            return false;
        }
        match e.kind {
            hir::ExprKind::DropTemps(inner) => self.is_place(inner),
            hir::ExprKind::Path(ref qpath) => {
                matches!(self.typeck.qpath_res(qpath, e.hir_id), Res::Local(_))
            }
            hir::ExprKind::Field(..) => true,
            hir::ExprKind::Unary(hir::UnOp::Deref, inner) => {
                self.is_plain_deref(e, inner) && self.is_place(inner)
            }
            _ => false,
        }
    }

    /// `*inner` of a reference that is not `Ghost`/`Tracked` and not an
    /// overloaded dereference: VIR keeps `inner` itself.
    fn is_plain_deref(&self, e: &hir::Expr<'_>, inner: &hir::Expr<'_>) -> bool {
        if self.typeck.is_method_call(e) {
            return false;
        }
        match self.typeck.expr_ty_adjusted(inner).kind() {
            ty::Ref(_, pointee, _) => !self.is_mode_wrapper(*pointee),
            _ => false,
        }
    }

    /// A boolean, an integer (`int` and `nat` included) or a character.
    fn is_smt_operand(&self, e: &hir::Expr<'_>) -> bool {
        let t = self.typeck.expr_ty_adjusted(e);
        match t.kind() {
            ty::Bool | ty::Int(_) | ty::Uint(_) | ty::Char => true,
            ty::Adt(adt, _) => matches!(
                self.cx.verus_item(adt.did()),
                Some(VerusItem::Int | VerusItem::Nat)
            ),
            _ => false,
        }
    }

    /// A cast: `x as T`, or its ghost-code form `spec_cast_integer(x)`.
    fn is_cast(&self, e: &hir::Expr<'_>) -> bool {
        match e.kind {
            hir::ExprKind::Cast(..) => true,
            hir::ExprKind::Call(func, _) => {
                self.callee(func).and_then(|d| self.cx.verus_item(d))
                    == Some(VerusItem::SpecCastInteger)
            }
            _ => false,
        }
    }

    /// `Ghost<T>` or `Tracked<T>`.
    fn is_mode_wrapper(&self, t: ty::Ty<'tcx>) -> bool {
        matches!(t.kind(), ty::Adt(adt, _) if matches!(
            self.cx.verus_item(adt.did()),
            Some(VerusItem::Ghost | VerusItem::Tracked)
        ))
    }

    /// The mode of the place `e` (a temporary when `e` is not a place), with
    /// Verus's check that exec code only uses exec places
    /// (`check_place_rec`).
    fn place_rec(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expect: Mode) -> M<Mode> {
        if let hir::ExprKind::DropTemps(inner) = e.kind {
            return self.place_rec(inner, outer, expect);
        }
        if !self.is_place(e) {
            let mode = self.expr_value(e, outer, expect)?;
            if self.block == Ghostness::Exec && mode != Mode::Exec && !self.is_unit(e) {
                return self.error(e.span, msg::temporary_in_exec(mode.name()));
            }
            return Ok(mode);
        }
        self.place_shape(e, outer, expect)
    }

    /// The mode of `e`, a variable, a field or a dereference, whatever
    /// attributes it carries, with the check of [`Self::place_rec`].
    fn place_shape(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expect: Mode) -> M<Mode> {
        let mode = match e.kind {
            hir::ExprKind::Path(ref qpath) => match self.typeck.qpath_res(qpath, e.hir_id) {
                Res::Local(hir_id) => self.var_mode(hir_id, e.span)?,
                _ => return self.unknown("a path that is not a variable", e.span),
            },
            hir::ExprKind::Field(base, _) => {
                let base_mode = self.place_rec(base, outer, expect)?;
                join(base_mode, self.field_mode(e, base)?)
            }
            hir::ExprKind::Unary(hir::UnOp::Deref, inner) => {
                return self.place_rec(inner, outer, expect)
            }
            _ => return self.unknown("a place of an unexpected kind", e.span),
        };
        if self.block == Ghostness::Exec && mode != Mode::Exec {
            return self.error(e.span, msg::place_in_exec(mode.name()));
        }
        Ok(mode)
    }

    /// A read of the place `e` (`check_place` with `PlaceAccess::Read`): the
    /// place's mode raised to the expected mode; spec in pure code.
    fn place_read(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expect: Mode) -> M<Mode> {
        let mode = self.place_rec(e, outer, expect)?;
        Ok(self.read_mode(mode, expect))
    }

    /// The mode of a read of a place of mode `mode`.
    fn read_mode(&self, mode: Mode, expect: Mode) -> Mode {
        if self.in_pure {
            Mode::Spec
        } else {
            join(mode, expect)
        }
    }

    /// `check_place_has_mode`: a `let` initializer.
    fn place_has_mode(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expected: Mode) -> M<()> {
        let mode = self.place_read(e, outer, expected)?;
        if !self.is_unit(e) && !le(mode, expected) {
            return self.error(e.span, msg::expr_mode(mode.name(), expected.name()));
        }
        Ok(())
    }

    /// The target of an assignment (`get_var_loc_mode`): the mode of the
    /// variable, raised by the modes of the fields on the way.
    fn loc_mode(&mut self, e: &'tcx hir::Expr<'tcx>) -> M<Mode> {
        match e.kind {
            hir::ExprKind::DropTemps(inner) => self.loc_mode(inner),
            hir::ExprKind::Path(ref qpath) => match self.typeck.qpath_res(qpath, e.hir_id) {
                Res::Local(hir_id) => {
                    let mode = self.var_mode(hir_id, e.span)?;
                    if self.block == Ghostness::Exec && mode != Mode::Exec {
                        return self.error(e.span, msg::EXEC_MUTATES_NON_EXEC);
                    }
                    Ok(mode)
                }
                _ => self.unknown("an assignment to something that is not a variable", e.span),
            },
            hir::ExprKind::Field(base, _) => {
                let base_mode = self.loc_mode(base)?;
                Ok(join(base_mode, self.field_mode(e, base)?))
            }
            hir::ExprKind::Unary(hir::UnOp::Deref, inner) if self.is_plain_deref(e, inner) => {
                self.loc_mode(inner)
            }
            _ => self.unknown("an assignment target of an unexpected kind", e.span),
        }
    }

    // ------------------------------------------------------------------
    // Expressions (`check_expr`)
    // ------------------------------------------------------------------

    /// `check_expr_has_mode`: `e`'s mode must not be above `expected`,
    /// unless `e` is `()`.
    fn has_mode(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expected: Mode) -> M<()> {
        let mode = self.expr(e, outer, expected)?;
        if !self.is_unit(e) && !le(mode, expected) {
            return self.error(e.span, msg::expr_mode(mode.name(), expected.name()));
        }
        Ok(())
    }

    /// The mode of `e` used as a value: a read of a place, or the value of
    /// any other expression.
    fn expr(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expect: Mode) -> M<Mode> {
        if let hir::ExprKind::DropTemps(inner) = e.kind {
            return self.expr(inner, outer, expect);
        }
        if self.is_place(e) {
            return self.place_read(e, outer, expect);
        }
        self.expr_value(e, outer, expect)
    }

    /// An expression that is not a place: its Verus attributes, then its
    /// adjustments, then the expression itself.
    fn expr_value(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expect: Mode) -> M<Mode> {
        let mut notes = 0;
        for (attr, span) in attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id)) {
            match attr {
                VerusAttr::ProofNote(_) | VerusAttr::CustomErr(_) => notes += 1,
                // Read by `expr_kind` as part of the block.
                VerusAttr::ProofBlock if matches!(e.kind, hir::ExprKind::Block(_, None)) => {}
                VerusAttr::OtherGhostBlock(name)
                    if name == PROOF_IN_SPEC && matches!(e.kind, hir::ExprKind::Block(_, None)) => {
                }
                // Changes how a cast is encoded, not its mode.
                VerusAttr::Unknown(name) if name == "verifier::truncate" && self.is_cast(e) => {}
                // A trigger reads its operand as spec, which pure code does
                // anyway; the annotations of a quantifier change no mode.
                VerusAttr::Trigger(_) if self.in_pure => {}
                VerusAttr::AutoTrigger | VerusAttr::AllTriggers => {}
                // Item attributes Verus accepts on an expression and
                // ignores there.
                VerusAttr::Mode(_)
                | VerusAttr::Rlimit(_)
                | VerusAttr::ExternalBody
                | VerusAttr::Opaque => {}
                // Change how a loop is encoded, not its modes.
                VerusAttr::LoopIsolation(_) | VerusAttr::AllowComplexInvariants
                    if matches!(e.kind, hir::ExprKind::Loop(..)) => {}
                other => return self.unknown(format!("{other:?} on an expression"), span),
            }
        }
        if notes > 1 {
            // Verus rejects a second note while building VIR.
            return self.unknown("two proof notes on an expression", e.span);
        }
        if notes == 1 {
            // `UnaryOpr::ProofNote`: its operand is spec code.
            let mode = self.expr_adjusted(e, Mode::Spec, Mode::Spec)?;
            if !self.is_unit(e) && !le(mode, Mode::Spec) {
                return self.error(e.span, msg::expr_mode(mode.name(), Mode::Spec.name()));
            }
            return Ok(Mode::Spec);
        }
        self.expr_adjusted(e, outer, expect)
    }

    /// `e` with its adjustments: only `!` coerced to another type
    /// (`ExprX::NeverToAny`) is modelled.
    fn expr_adjusted(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expect: Mode) -> M<Mode> {
        let adjustments = self.typeck.expr_adjustments(e);
        if !adjustments.is_empty() && adjustments.iter().all(|a| is_transparent_adjustment(a)) {
            // A shared borrow of a place reads it (`ReadPlace` with
            // `ImmutBor`); a dereference of a reference keeps the operand
            // (`strip_vir_ref_decoration`).
            if self.is_place_unadjusted(e) {
                let mode = self.place_shape(e, outer, expect)?;
                return Ok(self.read_mode(mode, expect));
            }
            return self.expr_kind(e, outer, expect);
        }
        if adjustments
            .iter()
            .any(|a| !matches!(a.kind, Adjust::NeverToAny))
        {
            return self.unknown("an implicit conversion", e.span);
        }
        if adjustments.is_empty() {
            return self.expr_kind(e, outer, expect);
        }
        let mode = self.expr_kind(e, outer, meet(expect, Mode::Proof))?;
        if mode == Mode::Spec {
            return self.error(e.span, msg::NEVER_TO_ANY_SPEC);
        }
        Ok(mode)
    }

    fn expr_kind(&mut self, e: &'tcx hir::Expr<'tcx>, outer: Mode, expect: Mode) -> M<Mode> {
        let span = e.span;
        match e.kind {
            hir::ExprKind::DropTemps(inner) => self.expr(inner, outer, expect),
            hir::ExprKind::Lit(_) => Ok(Mode::Exec),
            hir::ExprKind::Path(ref qpath) => match self.typeck.qpath_res(qpath, e.hir_id) {
                // Primitive constants are values, never places. Keep the
                // same actual core/owner/signature identity as body lowering.
                Res::Def(DefKind::AssocConst, definition)
                    if super::architecture::integer_constant(self.tcx, definition).is_some() =>
                {
                    Ok(Mode::Exec)
                }
                // A variable with attributes (a proof note): read as a place.
                Res::Local(_) => {
                    let mode = self.place_shape(e, outer, expect)?;
                    Ok(self.read_mode(mode, expect))
                }
                Res::Def(DefKind::Ctor(_, CtorKind::Const), constructor) => {
                    match self.typeck.expr_ty(e).kind() {
                        ty::Adt(adt, _) => {
                            let Some((_, variant)) = super::datatypes::constructor_variant(
                                *adt,
                                Res::Def(self.tcx.def_kind(constructor), constructor),
                            ) else {
                                return self.unknown(
                                    "a constructor outside its actual native datatype",
                                    span,
                                );
                            };
                            if !variant.fields.is_empty() {
                                return self.unknown("a unit constructor with native fields", span);
                            }
                            self.datatype_mode(*adt, span)
                        }
                        _ => self.unknown("a constructor of an unexpected type", span),
                    }
                }
                Res::Def(DefKind::Const | DefKind::AssocConst, def)
                    if def
                        .as_local()
                        .is_some_and(|local| self.cx.constant_mode(local).is_some()) =>
                {
                    match self.cx.constant_mode(def.expect_local()) {
                        Some(trust_vc_vcir::ConstMode::Dual) => Ok(Mode::Exec),
                        Some(trust_vc_vcir::ConstMode::Spec) => {
                            if self.block == Ghostness::Exec {
                                return self.error(span, "cannot read const with mode spec");
                            }
                            Ok(Mode::Spec)
                        }
                        _ => self.unknown("a constant without represented read semantics", span),
                    }
                }
                res => self.unknown(format!("a path to {}", res.descr()), span),
            },
            hir::ExprKind::Unary(hir::UnOp::Deref, inner) => self.deref(e, inner, outer, expect),
            hir::ExprKind::Unary(_, arg) => self.expr(arg, outer, expect),
            hir::ExprKind::Binary(_, lhs, rhs) => {
                // Rust operators on booleans, integers (Verus's `int` and
                // `nat` included, whose operator impls Verus reads as its
                // own operators) and characters are exec operators of VIR
                // (`BinaryOp` other than `Eq(Spec)` and `Implies`).
                if !self.is_smt_operand(lhs) || !self.is_smt_operand(rhs) {
                    return self.unknown("an operator on operands that are not primitive", span);
                }
                let m1 = self.expr(lhs, outer, Mode::Exec)?;
                let m2 = self.expr(rhs, outer, Mode::Exec)?;
                Ok(join(m1, m2))
            }
            hir::ExprKind::Call(func, args) => {
                if let hir::ExprKind::Path(qpath) = &func.kind {
                    if matches!(
                        self.typeck.qpath_res(qpath, func.hir_id),
                        Res::Def(DefKind::Ctor(_, CtorKind::Fn), _)
                    ) {
                        return self.tuple_ctor(e, func, args, outer, expect);
                    }
                }
                let Some(callee) = self.callee(func) else {
                    return self.unknown("a call of something that is not a named function", span);
                };
                if let Some(item) = self.cx.verus_item(callee) {
                    let args: Vec<&'tcx hir::Expr<'tcx>> = args.iter().collect();
                    return self.marker(e, callee, item, &args, outer, expect);
                }
                self.call(e, callee, args, outer)
            }
            hir::ExprKind::MethodCall(_, receiver, args, _) => {
                let Some(callee) = self.typeck.type_dependent_def_id(e.hir_id) else {
                    return self.unknown("an unresolved method call", span);
                };
                let mut all = vec![receiver];
                all.extend(args.iter());
                match self.cx.verus_item(callee) {
                    Some(item) => self.marker(e, callee, item, &all, outer, expect),
                    None => self.call_args(e, callee, &all, outer),
                }
            }
            hir::ExprKind::Block(block, None) => {
                let ghost = attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id))
                    .iter()
                    .any(|(attr, _)| *attr == VerusAttr::ProofBlock);
                if ghost {
                    return self.proof_block(e, block, outer, expect);
                }
                if is_proof_in_spec(self.tcx, e) {
                    return self.proof_in_spec(e, block, outer);
                }
                self.block_stmts(block.stmts, block.expr, outer, expect)
            }
            hir::ExprKind::If(cond, then_expr, else_expr) => {
                self.if_expr(e, cond, then_expr, else_expr, outer, expect)
            }
            hir::ExprKind::Struct(_, fields, tail) => {
                self.struct_ctor(e, fields, tail, outer, expect)
            }
            hir::ExprKind::Tup(elems) => {
                let mut mode = Mode::Exec;
                for elem in elems {
                    mode = self.ctor_arg(elem, Mode::Exec, mode, outer, expect)?;
                }
                Ok(mode)
            }
            hir::ExprKind::Cast(inner, _) => self.expr(inner, outer, expect),
            // A shared borrow reads its operand (`ReadPlace` with
            // `ImmutBor` of a place); VIR keeps it transparent.
            hir::ExprKind::AddrOf(hir::BorrowKind::Ref, rustc_ast::Mutability::Not, inner) => {
                self.expr(inner, outer, expect)
            }
            hir::ExprKind::Assign(lhs, rhs, _) | hir::ExprKind::AssignOp(_, lhs, rhs) => {
                self.assign(e, lhs, rhs, outer)
            }
            hir::ExprKind::Ret(value) => self.ret(e, value, outer),
            hir::ExprKind::Loop(block, _, source, header) => {
                self.loop_expr(block, source, header, outer)
            }
            // `ExprX::BreakOrContinue`: exec, and not in pure code.
            hir::ExprKind::Break(_, None) | hir::ExprKind::Continue(_) => {
                if self.in_pure {
                    return self.unknown("break or continue in pure code", span);
                }
                Ok(Mode::Exec)
            }
            hir::ExprKind::Field(..) => {
                let mode = self.place_shape(e, outer, expect)?;
                Ok(self.read_mode(mode, expect))
            }
            _ => self.unknown("an expression kind the mode checker does not model", span),
        }
    }

    /// Written fields run first. The base is then checked as a place even
    /// when every field is overridden, as in Verus's CtorUpdateTail rule.
    fn struct_ctor(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        fields: &'tcx [hir::ExprField<'tcx>],
        tail: hir::StructTailExpr<'tcx>,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        let ty::Adt(adt, _) = self.typeck.expr_ty(e).kind() else {
            return self.unknown("a struct expression of a non-ADT type", e.span);
        };
        let adt = *adt;
        if !self.cx.permits_adt_fields(adt.did()) {
            return self.unknown(
                "ADT constructor field modes are outside this producer slice",
                e.span,
            );
        }
        if !adt.is_struct() {
            return self.unknown(
                "a record enum constructor is outside the current native value slice",
                e.span,
            );
        }
        let mut mode = self.datatype_mode(adt, e.span)?;
        let mut written = vec![false; adt.non_enum_variant().fields.len()];
        for field in fields {
            let Some(index) = self.typeck.opt_field_index(field.hir_id) else {
                return self.unknown("a struct field without a compiler index", field.span);
            };
            let Some(decl) = adt.non_enum_variant().fields.get(index) else {
                return self.unknown("a struct field outside its type", field.span);
            };
            written[index.as_usize()] = true;
            let field_mode = self.constructor_field_mode(decl, field.span)?;
            mode = self.ctor_arg(field.expr, field_mode, mode, outer, expect)?;
        }
        let base = match tail {
            hir::StructTailExpr::None => return Ok(mode),
            hir::StructTailExpr::Base(base) => base,
            _ => {
                return self.unknown(
                    "a struct expression with default or erroneous fields",
                    e.span,
                )
            }
        };
        let mut taken = Vec::new();
        let mut base_expect = if self.block == Ghostness::Exec {
            Mode::Exec
        } else {
            Mode::Spec
        };
        for (index, field) in adt.non_enum_variant().fields.iter().enumerate() {
            if !written[index] {
                let field_mode = self.constructor_field_mode(field, base.span)?;
                taken.push(field_mode);
                let expected = join(expect, field_mode);
                if self.block != Ghostness::Exec && le(expected, base_expect) {
                    base_expect = expected;
                }
            }
        }
        let base_mode = self.place_rec(base, outer, base_expect)?;
        for field_mode in taken {
            let argument_mode = join(base_mode, field_mode);
            if !le(argument_mode, field_mode) {
                mode = join(mode, argument_mode);
            }
        }
        Ok(mode)
    }

    /// A tuple struct or enum variant applied to its fields (`ExprX::Ctor`),
    /// as a struct expression.
    fn tuple_ctor(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        function: &'tcx hir::Expr<'tcx>,
        args: &'tcx [hir::Expr<'tcx>],
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        let ty::Adt(adt, _) = self.typeck.expr_ty(e).kind() else {
            return self.unknown("a constructor of a non-ADT type", e.span);
        };
        let adt = *adt;
        if !self.cx.permits_adt_fields(adt.did()) {
            return self.unknown(
                "ADT constructor field modes are outside this producer slice",
                e.span,
            );
        }
        let mut mode = self.datatype_mode(adt, e.span)?;
        let hir::ExprKind::Path(qpath) = &function.kind else {
            return self.unknown("a constructor without its native path", e.span);
        };
        let Some((_, variant)) = super::datatypes::constructor_variant(
            adt,
            self.typeck.qpath_res(qpath, function.hir_id),
        ) else {
            return self.unknown("a constructor outside its actual native datatype", e.span);
        };
        let fields = &variant.fields;
        if fields.len() != args.len() {
            return self.unknown("a constructor with another number of fields", e.span);
        }
        for (field, arg) in fields.iter().zip(args) {
            let Some(local) = field.did.as_local() else {
                return self.unknown("a field of a struct of another crate", arg.span);
            };
            let field_mode =
                self.declared_mode(self.tcx.local_def_id_to_hir_id(local), Mode::Exec, arg.span)?;
            mode = self.ctor_arg(arg, field_mode, mode, outer, expect)?;
        }
        Ok(mode)
    }

    /// One field of a constructor (`ExprX::Ctor`): a field value above the
    /// field's mode raises the mode of the whole value.
    fn ctor_arg(
        &mut self,
        arg: &'tcx hir::Expr<'tcx>,
        field_mode: Mode,
        mode: Mode,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        let arg_mode = self.expr(arg, join(outer, field_mode), join(expect, field_mode))?;
        Ok(if le(arg_mode, field_mode) {
            mode
        } else {
            join(mode, arg_mode)
        })
    }

    /// `*inner` that is not a place: `*old(x)`, or a dereference of a value.
    fn deref(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        inner: &'tcx hir::Expr<'tcx>,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        if let hir::ExprKind::Call(func, [_]) = inner.kind {
            if self.callee(func).and_then(|d| self.cx.verus_item(d)) == Some(VerusItem::Old) {
                // `ExprX::VarAt`: spec, and not allowed in exec code.
                if self.in_pure {
                    return Ok(Mode::Spec);
                }
                if self.block == Ghostness::Exec {
                    return self.error(inner.span, msg::OLD_IN_EXEC);
                }
                return Ok(Mode::Spec);
            }
        }
        if !self.is_plain_deref(e, inner) {
            return self.unknown("a dereference of something that is not a reference", e.span);
        }
        self.expr(inner, outer, expect)
    }

    /// `ExprX::Ghost` of a `proof { .. }` block.
    fn proof_block(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        block: &'tcx hir::Block<'tcx>,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        if self.block == Ghostness::Ghost {
            return self.error(e.span, msg::ALREADY_PROOF);
        }
        if !self.typeck.expr_ty(e).is_unit() {
            return self.error(e.span, messages::PROOF_BLOCK_NOT_UNIT);
        }
        let saved = self.block;
        self.block = Ghostness::Ghost;
        let inner_outer = if outer == Mode::Exec {
            Mode::Proof
        } else {
            outer
        };
        let mode = self.block_stmts(
            block.stmts,
            block.expr,
            inner_outer,
            join(expect, Mode::Spec),
        );
        self.block = saved;
        mode
    }

    /// `ExprX::ProofInSpec`: a `proof { .. }` block in spec code, proof code
    /// of type `()`.
    fn proof_in_spec(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        block: &'tcx hir::Block<'tcx>,
        outer: Mode,
    ) -> M<Mode> {
        match (self.block, outer) {
            (Ghostness::Ghost, Mode::Spec) => {}
            (Ghostness::Ghost, Mode::Proof) => return self.error(e.span, msg::ALREADY_PROOF),
            _ => return self.unknown("a proof block in spec code outside ghost code", e.span),
        }
        if !self.typeck.expr_ty(e).is_unit() {
            return self.error(e.span, messages::PROOF_BLOCK_NOT_UNIT);
        }
        let saved = (self.in_pure, self.in_proof_in_spec);
        self.in_pure = false;
        self.in_proof_in_spec = true;
        let mode = self.block_stmts(block.stmts, block.expr, Mode::Proof, Mode::Spec);
        (self.in_pure, self.in_proof_in_spec) = saved;
        mode
    }

    /// `ExprX::If`.
    fn if_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        cond: &'tcx hir::Expr<'tcx>,
        then_expr: &'tcx hir::Expr<'tcx>,
        else_expr: Option<&'tcx hir::Expr<'tcx>>,
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        let cond = match cond.kind {
            hir::ExprKind::DropTemps(inner) => inner,
            _ => cond,
        };
        if matches!(cond.kind, hir::ExprKind::Let(..)) {
            return self.unknown("`if let`", cond.span);
        }
        let cond_expect = self.stmt_expect();
        let cond_mode = self.expr(cond, outer, cond_expect)?;
        if self.block == Ghostness::Exec && cond_mode != Mode::Exec {
            return self.error(e.span, msg::CONDITION_NOT_EXEC);
        }
        let branch = if outer == Mode::Exec && cond_mode == Mode::Spec {
            Mode::Proof
        } else {
            outer
        };
        let then_mode = self.expr(then_expr, branch, expect)?;
        match else_expr {
            Some(else_expr) => {
                let else_mode = self.expr(else_expr, branch, expect)?;
                Ok(join(then_mode, else_mode))
            }
            None => Ok(then_mode),
        }
    }

    /// `ExprX::Loop`: exec code only; the condition and the body are exec,
    /// then the invariants and the measure are pure spec code, in Verus's
    /// order (`invariant_except_break`, `invariant`, `ensures`, then
    /// `decreases`).
    fn loop_expr(
        &mut self,
        block: &'tcx hir::Block<'tcx>,
        source: hir::LoopSource,
        header: Span,
        outer: Mode,
    ) -> M<Mode> {
        if self.block == Ghostness::Ghost {
            return self.error(header, msg::LOOP_IN_GHOST);
        }
        let (cond, body) = match source {
            hir::LoopSource::While => match (block.stmts, block.expr) {
                (
                    [],
                    Some(hir::Expr {
                        kind: hir::ExprKind::If(cond, then_expr, Some(_)),
                        ..
                    }),
                ) => match then_expr.kind {
                    hir::ExprKind::Block(body, None) => (Some(*cond), body),
                    _ => return self.unknown("a while loop of an unexpected shape", header),
                },
                _ => return self.unknown("a while loop of an unexpected shape", header),
            },
            hir::LoopSource::Loop => (None, block),
            hir::LoopSource::ForLoop => return self.unknown("a for loop", header),
        };
        if let Some(cond) = cond {
            self.has_mode(cond, outer, Mode::Exec)?;
        }
        // The header statements lead the body.
        let mut specs: [Vec<&'tcx hir::Expr<'tcx>>; 3] = [Vec::new(), Vec::new(), Vec::new()];
        let mut measure: Vec<&'tcx hir::Expr<'tcx>> = Vec::new();
        let mut header_len = 0;
        for stmt in body.stmts {
            let hir::StmtKind::Semi(e) = stmt.kind else {
                break;
            };
            let hir::ExprKind::Call(func, [arg]) = e.kind else {
                break;
            };
            let Some(def_id) = self.callee(func) else {
                break;
            };
            let Some(item) = self.cx.verus_item(def_id) else {
                break;
            };
            if !item.is_header() {
                break;
            }
            let name = self.tcx.item_name(def_id);
            let slot = match (item, name.as_str()) {
                (VerusItem::OtherHeader, "invariant_except_break") => 0,
                (VerusItem::OtherHeader, "invariant") => 1,
                (VerusItem::Ensures, _) => 2,
                (VerusItem::OtherHeader, "decreases") => {
                    match arg.kind {
                        hir::ExprKind::Tup(parts) => measure.extend(parts.iter()),
                        _ => measure.push(arg),
                    }
                    header_len += 1;
                    continue;
                }
                _ => return self.unknown("a loop header the reader does not read", e.span),
            };
            specs[slot].extend(self.clause_elements(arg, item));
            header_len += 1;
        }
        let body_mode =
            self.block_stmts(&body.stmts[header_len..], body.expr, outer, Mode::Exec)?;
        let body_unit = body.expr.is_none_or(|tail| self.is_unit(tail));
        if !body_unit && !le(body_mode, Mode::Exec) {
            return self.error(
                body.span,
                msg::expr_mode(body_mode.name(), Mode::Exec.name()),
            );
        }
        let saved = (self.block, self.in_pure);
        self.block = Ghostness::Ghost;
        self.in_pure = true;
        let mut result = Ok(());
        for clause in specs.iter().flatten().chain(&measure) {
            result = self.has_mode(clause, Mode::Spec, Mode::Spec);
            if result.is_err() {
                break;
            }
        }
        (self.block, self.in_pure) = saved;
        result?;
        Ok(Mode::Exec)
    }

    /// `ExprX::Assign` (with or without an operator).
    fn assign(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        outer: Mode,
    ) -> M<Mode> {
        if self.in_pure {
            return self.error(e.span, msg::ASSIGN_IN_PURE);
        }
        // `let tracked x = v` is `let x; .. { let t = v; x = t; }`: the
        // assignment of a variable to a variable whose mode is not decided
        // yet gives it the other's mode.
        if let (hir::ExprKind::Path(ref lq), hir::ExprKind::Path(ref rq)) = (&lhs.kind, &rhs.kind) {
            if let (Res::Local(xl), Res::Local(xr)) = (
                self.typeck.qpath_res(lq, lhs.hir_id),
                self.typeck.qpath_res(rq, rhs.hir_id),
            ) {
                if matches!(self.vars.get(&xl), Some(VarMode::Infer)) && self.is_place(rhs) {
                    let mode = self.var_mode(xr, rhs.span)?;
                    self.vars.insert(xl, VarMode::Mode(mode));
                }
            }
        }
        let var_mode = self.loc_mode(lhs)?;
        if !le(outer, var_mode) {
            return self.error(e.span, msg::assign_mode(var_mode.name(), outer.name()));
        }
        self.has_mode(rhs, outer, var_mode)?;
        Ok(var_mode)
    }

    /// `ExprX::Return`.
    fn ret(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        value: Option<&'tcx hir::Expr<'tcx>>,
        outer: Mode,
    ) -> M<Mode> {
        if self.fun_mode == Mode::Exec && self.block == Ghostness::Ghost {
            return self.error(e.span, msg::RETURN_FROM_NON_EXEC);
        }
        if self.in_assert_by {
            return self.error(e.span, msg::RETURN_IN_ASSERT_BY);
        }
        if self.in_proof_in_spec {
            return self.error(e.span, msg::RETURN_IN_PROOF_IN_SPEC);
        }
        if self.in_pure {
            return self.error(e.span, msg::RETURN_IN_PURE);
        }
        match (value, self.ret_mode) {
            (None, _) => {}
            (Some(v), None) if self.is_unit(v) => {}
            (Some(v), None) => {
                return self.unknown(
                    "a value returned from a function without a return type",
                    v.span,
                )
            }
            (Some(v), Some(ret_mode)) => self.has_mode(v, outer, ret_mode)?,
        }
        Ok(Mode::Exec)
    }

    /// A call of a Verus function of this crate (`CallTarget::Fun`).
    fn call(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        callee: DefId,
        args: &'tcx [hir::Expr<'tcx>],
        outer: Mode,
    ) -> M<Mode> {
        let args: Vec<&'tcx hir::Expr<'tcx>> = args.iter().collect();
        self.call_args(e, callee, &args, outer)
    }

    /// A call of `callee` with `args`, a method call's receiver first
    /// (`ExprX::Call`). A call of a trait method is checked with the
    /// declaration's modes, as Verus does.
    fn call_args(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        callee: DefId,
        args: &[&'tcx hir::Expr<'tcx>],
        outer: Mode,
    ) -> M<Mode> {
        let span = e.span;
        let sig = call_modes_with_context(self.cx, callee, span).map_err(Stop::Unknown)?;
        if (sig.mode == Mode::Exec) != (self.block == Ghostness::Exec) || !le(outer, sig.mode) {
            let name = self.cx.friendly_fn_path(callee);
            return self.error(span, msg::call_mode(&name, sig.mode.name()));
        }
        if args.len() != sig.params.len() {
            return self.unknown("a call with the wrong number of arguments", span);
        }
        for (arg, facts) in args.iter().zip(&sig.params) {
            if facts.mutable_reference {
                return self.unknown("an argument for a `&mut` parameter", arg.span);
            }
            let param_mode = facts.mode;
            self.has_mode(arg, join(outer, param_mode), param_mode)?;
        }
        Ok(sig.ret)
    }

    /// A call of a Verus marker.
    fn marker(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        callee: DefId,
        item: VerusItem,
        args: &[&'tcx hir::Expr<'tcx>],
        outer: Mode,
        expect: Mode,
    ) -> M<Mode> {
        let span = e.span;
        match (item, args) {
            // The pinned diagnostic item is Spec, with two Spec parameters.
            // It is external, so no local/imported signature receipt exists.
            // Outside ensures it is retained: check BOTH real arguments.
            (VerusItem::ConstrainType, [first, second]) => {
                if self.block == Ghostness::Exec || !le(outer, Mode::Spec) {
                    let name = self.cx.friendly_fn_path(callee);
                    return self.error(span, msg::call_mode(&name, Mode::Spec.name()));
                }
                for arg in [first, second] {
                    self.has_mode(arg, join(outer, Mode::Spec), Mode::Spec)?;
                }
                Ok(Mode::Spec)
            }
            (VerusItem::ArchWordBits, []) => Ok(Mode::Spec),
            (VerusItem::GetVariantField, [receiver, variant, field]) => {
                self.variant_field(e, callee, receiver, variant, field, outer, expect)
            }
            (VerusItem::IsVariant, [receiver, variant]) => {
                self.variant_test(e, callee, receiver, variant, outer, expect)
            }
            // `ExprX::Closure`: the authenticated conversion marker makes a
            // Spec closure, not an arbitrary Rust executable closure.
            (VerusItem::ClosureToFnSpec, [closure]) => self.spec_closure(closure),
            // `ExprX::AssertAssume`: ghost code only; the argument is pure.
            (VerusItem::Assert | VerusItem::Assume, [arg]) => {
                if self.block == Ghostness::Exec {
                    return self.error(span, msg::ASSERT_IN_EXEC);
                }
                let saved = self.in_pure;
                self.in_pure = true;
                let result = self.has_mode(arg, Mode::Spec, Mode::Spec);
                self.in_pure = saved;
                result?;
                Ok(outer)
            }
            (VerusItem::Admit, []) => {
                if self.block == Ghostness::Exec {
                    return self.error(span, msg::ASSERT_IN_EXEC);
                }
                Ok(outer)
            }
            // `ExprX::AssertBy`: ghost code only; the condition is pure and
            // the proof is proof code.
            (VerusItem::AssertBy, [cond, proof]) => {
                if self.block == Ghostness::Exec {
                    let mut error = UserError::new(Phase::Modes, span, msg::ASSERT_BY_IN_EXEC);
                    error.help = Some(msg::ASSERT_BY_IN_EXEC_HELP.to_string());
                    return Err(Stop::Error(error));
                }
                let saved = self.in_pure;
                self.in_pure = true;
                let result = self.has_mode(cond, Mode::Spec, Mode::Spec);
                self.in_pure = saved;
                result?;
                let saved = (self.in_pure, self.in_assert_by);
                self.in_pure = false;
                self.in_assert_by = true;
                let result = self.expr(proof, Mode::Proof, Mode::Proof);
                (self.in_pure, self.in_assert_by) = saved;
                result?;
                Ok(Mode::Proof)
            }
            (VerusItem::AssertBitvectorBy, [proof]) => {
                if self.block == Ghostness::Exec {
                    return self.error(span, msg::ASSERT_IN_EXEC);
                }
                self.assert_bitvector_body(proof)?;
                Ok(Mode::Proof)
            }
            // Fuel 0 is a `hide`, a header of the function; any other fuel
            // is `ExprX::Fuel`, ghost code only.
            (VerusItem::RevealHide, [_, fuel]) => {
                let hide = matches!(
                    fuel.kind,
                    hir::ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::ast::LitKind::Int(n, _) if n.get() == 0)
                );
                if !hide && self.block == Ghostness::Exec {
                    let mut error = UserError::new(Phase::Modes, span, msg::REVEAL_IN_EXEC);
                    error.help = Some(msg::REVEAL_IN_EXEC_HELP.to_string());
                    return Err(Stop::Error(error));
                }
                Ok(outer)
            }
            // `BinaryOp::Implies`: spec, with spec operands.
            (VerusItem::Imply, [lhs, rhs]) => {
                self.expr(lhs, Mode::Spec, Mode::Spec)?;
                self.expr(rhs, Mode::Spec, Mode::Spec)?;
                Ok(Mode::Spec)
            }
            // `BinaryOp::Eq(Mode::Spec)`: spec; its operands keep the outer
            // mode.
            (VerusItem::SpecEq | VerusItem::Equal, [lhs, rhs]) => {
                self.expr(lhs, outer, Mode::Spec)?;
                self.expr(rhs, outer, Mode::Spec)?;
                Ok(Mode::Spec)
            }
            // Arithmetic, comparisons and bit operations become exec
            // operators of VIR, spec only through their operands.
            (
                VerusItem::SpecOrd(_)
                | VerusItem::SpecArith(_)
                | VerusItem::SpecBitwise(_)
                | VerusItem::BuiltinArith(_),
                [lhs, rhs],
            ) => {
                let m1 = self.expr(lhs, outer, Mode::Exec)?;
                let m2 = self.expr(rhs, outer, Mode::Exec)?;
                Ok(join(m1, m2))
            }
            (VerusItem::SpecNeg, [arg]) => self.expr(arg, outer, Mode::Exec),
            (
                VerusItem::SpecLiteralInteger
                | VerusItem::SpecLiteralInt
                | VerusItem::SpecLiteralNat,
                [_],
            ) => Ok(Mode::Exec),
            (VerusItem::SpecCastInteger, [arg]) => self.expr(arg, outer, expect),
            // A height comparison of integers becomes comparisons of its
            // operands, whose modes Verus joins; in ghost code that is
            // spec.
            // A chained comparison is spec code (`record_spec_fn`), with
            // spec operands.
            (VerusItem::Chained(_), operands) if self.block == Ghostness::Ghost => {
                for operand in operands {
                    self.expr(operand, Mode::Spec, Mode::Spec)?;
                }
                Ok(Mode::Spec)
            }
            (VerusItem::IsSmallerThan | VerusItem::IsSmallerThanLexicographic, [lhs, rhs])
                if self.block == Ghostness::Ghost =>
            {
                self.expr(lhs, Mode::Spec, Mode::Spec)?;
                self.expr(rhs, Mode::Spec, Mode::Spec)?;
                Ok(Mode::Spec)
            }
            // `ExprX::Quant` and `ExprX::Choose`: ghost code only; the
            // variables are spec and the body is pure spec code.
            (VerusItem::Forall | VerusItem::Exists, [arg]) => {
                if self.block == Ghostness::Exec {
                    return self.error(span, msg::QUANT_IN_EXEC);
                }
                self.binder(arg, &mut |this, body| {
                    this.has_mode(body, Mode::Spec, Mode::Spec)
                })?;
                Ok(Mode::Spec)
            }
            (VerusItem::Choose | VerusItem::ChooseTuple, [arg]) => {
                if self.block == Ghostness::Exec {
                    return self.error(span, msg::CHOOSE_IN_EXEC);
                }
                self.binder(arg, &mut |this, body| {
                    this.has_mode(body, Mode::Spec, Mode::Spec)
                })?;
                Ok(Mode::Spec)
            }
            // `ExprX::WithTriggers`: spec trigger terms and body.
            (VerusItem::WithTriggers, [groups, body]) => {
                let hir::ExprKind::Tup(groups) = groups.kind else {
                    return self.unknown("triggers that are not a tuple", groups.span);
                };
                for group in groups {
                    let hir::ExprKind::Tup(terms) = group.kind else {
                        return self.unknown("a trigger group that is not a tuple", group.span);
                    };
                    for term in terms {
                        self.has_mode(term, Mode::Spec, Mode::Spec)?;
                    }
                }
                self.has_mode(body, Mode::Spec, Mode::Spec)?;
                Ok(Mode::Spec)
            }
            // `ExprX::AssertBy` with variables: ghost code only; the
            // variables are spec, `requires` and `ensures` pure spec code,
            // and the proof proof code in which proof variables read as
            // spec.
            (VerusItem::AssertForallBy, [arg]) => {
                if self.block == Ghostness::Exec {
                    let mut error = UserError::new(Phase::Modes, span, msg::ASSERT_BY_IN_EXEC);
                    error.help = Some(msg::ASSERT_BY_IN_EXEC_HELP.to_string());
                    return Err(Stop::Error(error));
                }
                self.binder(arg, &mut |this, body| this.assert_forall_body(body))?;
                Ok(Mode::Proof)
            }
            _ => self.unknown(format!("the Verus item {item:?}"), span),
        }
    }

    /// The Spec lambda rule of modes.rs, after the rust-to-VIR shape checks.
    /// Captured values retain their existing modes; only this closure's actual
    /// parameter bindings are introduced as Spec in the fresh variable scope.
    fn spec_closure(&mut self, expr: &'tcx hir::Expr<'tcx>) -> M<Mode> {
        if self.block == Ghostness::Exec {
            // Verus rejects this while building VIR. Keep that earlier-phase
            // error outside a successful mode receipt rather than relabeling
            // it as a later mode error.
            return self.unknown(
                "a Spec closure in exec code is rejected before mode checking",
                expr.span,
            );
        }
        let hir::ExprKind::Closure(closure) = expr.kind else {
            return self.unknown(
                "a Spec conversion whose argument is not a closure",
                expr.span,
            );
        };
        if closure.fn_decl.c_variadic()
            || closure.fn_decl.implicit_self() != hir::ImplicitSelfKind::None
            || closure.fn_decl.splatted().is_some()
            || !closure.bound_generic_params.is_empty()
            || !matches!(closure.binder, hir::ClosureBinder::Default)
            || !matches!(closure.kind, hir::ClosureKind::Closure)
            || !matches!(closure.constness, hir::Constness::NotConst)
            || !closure.explicit_captures.is_empty()
        {
            return self.unknown(
                "a Spec closure has an unsupported native binder/capture form",
                expr.span,
            );
        }
        let body = self.tcx.hir_body(closure.body);
        for parameter in body.params {
            // rust_to_vir_expr::closure_to_vir permits only unmarked/Exec
            // parameter declarations before VIR gives them Spec semantics.
            let declared = declared_mode(self.tcx, parameter.hir_id, Mode::Exec, parameter.span)
                .map_err(Stop::Unknown)?;
            if declared.mode != Mode::Exec {
                return self.unknown(
                    "a non-exec closure parameter is rejected before mode checking",
                    parameter.span,
                );
            }
        }
        let saved = self.vars.clone();
        let result = self.binder(expr, &mut |this, value| {
            this.has_mode(value, Mode::Spec, Mode::Spec)
        });
        self.vars = saved;
        result?;
        Ok(Mode::Spec)
    }

    /// The closure of a quantifier, choice or `assert forall`: its
    /// parameters are spec variables, and `body` checks its body.
    fn binder(
        &mut self,
        arg: &'tcx hir::Expr<'tcx>,
        body: &mut dyn FnMut(&mut Self, &'tcx hir::Expr<'tcx>) -> M<()>,
    ) -> M<()> {
        let mut arg = arg;
        if let hir::ExprKind::Call(func, [inner]) = arg.kind {
            if self.callee(func).and_then(|d| self.cx.verus_item(d))
                == Some(VerusItem::ClosureToFnSpec)
            {
                arg = inner;
            }
        }
        let hir::ExprKind::Closure(closure) = arg.kind else {
            return self.unknown("a quantifier whose argument is not a closure", arg.span);
        };
        let closure_body = self.tcx.hir_body(closure.body);
        for param in closure_body.params {
            let PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, _, None) = param.pat.kind
            else {
                return self.unknown(
                    "a quantifier variable that is not a plain name",
                    param.pat.span,
                );
            };
            self.vars.insert(pat_hir, VarMode::Mode(Mode::Spec));
        }
        let saved = self.in_pure;
        self.in_pure = true;
        let result = body(self, closure_body.value);
        self.in_pure = saved;
        result
    }

    /// The body of `assert_forall_by`: `requires` and `ensures`, then the
    /// proof.
    fn assert_forall_body(&mut self, body: &'tcx hir::Expr<'tcx>) -> M<()> {
        let hir::ExprKind::Block(block, None) = body.kind else {
            return self.unknown("an assert forall whose body is not a block", body.span);
        };
        let mut header = 0;
        for stmt in block.stmts {
            let (hir::StmtKind::Semi(call) | hir::StmtKind::Expr(call)) = stmt.kind else {
                break;
            };
            let Some((item, clause)) = self.assertion_header_clause(call) else {
                break;
            };
            self.clause_list(clause, item)?;
            header += 1;
        }
        let saved = (self.in_pure, self.in_assert_by);
        self.in_pure = false;
        self.in_assert_by = true;
        let result = self.block_stmts(&block.stmts[header..], block.expr, Mode::Proof, Mode::Proof);
        (self.in_pure, self.in_assert_by) = saved;
        result.map(|_| ())
    }

    fn assert_bitvector_body(&mut self, body: &'tcx hir::Expr<'tcx>) -> M<()> {
        let hir::ExprKind::Block(block, None) = body.kind else {
            return self.unknown(
                "an isolated BV assertion whose argument is not a block",
                body.span,
            );
        };
        let mut header = 0;
        for stmt in block.stmts {
            let (hir::StmtKind::Semi(call) | hir::StmtKind::Expr(call)) = stmt.kind else {
                break;
            };
            let Some((item, clause)) = self.assertion_header_clause(call) else {
                break;
            };
            self.clause_list(clause, item)?;
            header += 1;
        }
        // An omitted final semicolon leaves the last header in `block.expr`.
        // It has the same pure Spec obligation as a statement header; it is
        // not a call of the function-level header builtin in Proof mode.
        let mut tail = block.expr;
        if header == block.stmts.len() {
            if let Some((item, clause)) = tail.and_then(|call| self.assertion_header_clause(call)) {
                self.clause_list(clause, item)?;
                tail = None;
            }
        }
        let saved = self.in_pure;
        self.in_pure = false;
        let result = self.block_stmts(&block.stmts[header..], tail, Mode::Proof, Mode::Proof);
        self.in_pure = saved;
        result.map(|_| ())
    }

    fn assertion_header_clause(
        &self,
        call: &'tcx hir::Expr<'tcx>,
    ) -> Option<(VerusItem, &'tcx hir::Expr<'tcx>)> {
        let hir::ExprKind::Call(func, [clause]) = call.kind else {
            return None;
        };
        let item @ (VerusItem::Requires | VerusItem::Ensures) =
            self.callee(func).and_then(|id| self.cx.verus_item(id))?
        else {
            return None;
        };
        Some((item, clause))
    }
}

/// The attribute of a `proof { .. }` block in spec code.
pub(crate) const PROOF_IN_SPEC: &str = "verifier::proof_in_spec";

/// Is `e` a `proof { .. }` block in spec code?
pub(crate) fn is_proof_in_spec(tcx: TyCtxt<'_>, e: &hir::Expr<'_>) -> bool {
    matches!(e.kind, hir::ExprKind::Block(_, None))
        && attrs::verus_attrs(tcx.hir_attrs(e.hir_id)).iter().any(
            |(attr, _)| matches!(attr, VerusAttr::OtherGhostBlock(name) if name == PROOF_IN_SPEC),
        )
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL: [Mode; 3] = [Mode::Exec, Mode::Proof, Mode::Spec];

    #[test]
    fn lattice_is_exec_below_proof_below_spec() {
        assert!(le(Mode::Exec, Mode::Proof) && le(Mode::Proof, Mode::Spec));
        assert!(!le(Mode::Spec, Mode::Proof) && !le(Mode::Proof, Mode::Exec));
        for a in ALL {
            assert!(le(a, a));
            for b in ALL {
                let j = join(a, b);
                let m = meet(a, b);
                assert!(le(a, j) && le(b, j), "{a:?} {b:?}");
                assert!(le(m, a) && le(m, b), "{a:?} {b:?}");
                assert_eq!(j, join(b, a));
                assert_eq!(m, meet(b, a));
                assert!(j == a || j == b);
                assert!(m == a || m == b);
            }
        }
        assert_eq!(join(Mode::Exec, Mode::Proof), Mode::Proof);
        assert_eq!(meet(Mode::Spec, Mode::Proof), Mode::Proof);
    }

    #[test]
    fn default_variable_modes() {
        assert_eq!(Checker::default_var_mode(Mode::Exec), Mode::Exec);
        assert_eq!(Checker::default_var_mode(Mode::Proof), Mode::Spec);
        assert_eq!(Checker::default_var_mode(Mode::Spec), Mode::Spec);
    }
}
