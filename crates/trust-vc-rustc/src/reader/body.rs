//! Lowering one function: its signature, its header clauses and its body.
//!
//! # Contexts
//!
//! Every expression is lowered in one of three contexts ([`Ctx`]):
//!
//! * `Exec`: exec code outside ghost blocks. Machine-integer `+ - * / %`
//!   get a check site (overflow, division by zero); assignments to
//!   immutable locals are left to rustc's borrow checker.
//! * `Proof`: a proof function body, or a `proof { .. }` block in exec code.
//!   Machine-integer arithmetic wraps into its type, as in Verus's ghost
//!   code (`OverflowBehavior::Truncate`).
//! * `Spec`: clauses, `assert`/`assume` arguments and spec function bodies.
//!   Pure: nothing here may produce a statement.
//!
//! # Effects
//!
//! VcIR expressions are pure. An expression with effects (a call of an exec
//! or proof function, an assignment inside a block, a short-circuit operator
//! whose right side assigns) is flattened: its effects are emitted as
//! statements into the caller's statement list, in evaluation order, and the
//! value it computes is read back from a temporary.
//!
//! # Outcome
//!
//! A function is either lowered completely, or stops at the first thing that
//! decides its fate ([`FnProblem`]): a refusal, a Verus error that Verus
//! reports while building VIR (after which Verus reads no further either),
//! or an exec assignment that rustc's borrow checker rejects. Verus errors
//! from later phases do not stop lowering; they are collected and reported
//! with the phase that owns them.

use std::collections::{HashMap, HashSet};

use rustc_ast::ast::LitIntType;
use rustc_ast::ast::LitKind as AstLitKind;
use rustc_ast::{BindingMode, ByRef};
use rustc_hir::def::{CtorKind, CtorOf, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId, ModId};
use rustc_hir::{self as hir, BinOpKind, HirId, ImplicitSelfKind, LocalSource, PatKind, QPath};
use rustc_middle::ty::adjustment::{
    Adjust, Adjustment, AutoBorrow, AutoBorrowMutability, DerefAdjustKind,
};
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt, TypeckResults};
use rustc_span::Span;

use trust_vc_vcir::wf::msg_not_mutable;
use trust_vc_vcir::{
    BinOp, Block, Body, CastKind, Clause, ClauseAttrs, ConstMode, DeclProphecy, DefOrder, Expr,
    ExprKind, FnAttrs, FnDecl, FnKind, FnRole, IntLit, IntRange, InvariantKind, Lit, LocalDecl,
    LocalId, LocalKind, Loop, LoopCond, LoopId, LoopInvariant, LoopSites, Mode, Place, Projection,
    QuantKind, SiteId, SpanId, Stmt, StmtKind, Ty, UnOp, UnwindSpec,
};

use super::attr_walk::{self, AttrFinding};
use super::attrs::{self, AttrProblem, LoopSettings, VerusAttr};
use super::{Cx, Refusal, UserError};
use crate::messages::{self, Phase};
use crate::verus_items::{BuiltinArith, ChainOp, OrdOp, SpecArith, SpecBitwise, VerusItem};
use crate::vtyp::spec_eq_compatible;

mod assignment_values;
mod binding_modes;
mod bitvector;
mod constructors;
mod copy_premises;
mod enum_casts;
mod header_binding_scope;
mod matches;
mod patterns;
mod primitive_eq;
mod quant;
mod reference_values;
mod returns;
mod seq;
mod spec_bindings;
mod structs;
mod unwind;
mod variant_fields;

/// Why a function was not lowered completely.
#[derive(Debug, Clone)]
pub(crate) enum FnProblem {
    /// Something the reader does not handle.
    Refused(Refusal),
    /// A current native constant occurrence cannot be lowered without its
    /// canonical completed modes. This remains a denial; only the same
    /// function's actual mode error can take precedence over this reason.
    MissingConstantModes(Refusal),
    /// A Verus error from the VIR-building phase; Verus reads no further.
    Rejected(UserError),
}

/// The result of reading one function.
pub(crate) struct FnOutcome {
    /// The lowered function, or why there is none.
    pub result: Result<FnDecl, FnProblem>,
    /// Verus errors of later phases found while lowering. They are reported
    /// whatever `result` is.
    pub errors: Vec<UserError>,
    /// The first exec assignment to an immutable, initialized local. rustc's
    /// borrow checker reports it in the erase run, and Verus's lifetime
    /// check stops before verification; the function is still lowered so
    /// that errors of earlier phases are found.
    pub deferred: Option<Span>,
    /// A refusal that only verification needs: the function was read
    /// completely, but the VC generator cannot use it as read. It stands
    /// unless Verus rejects the crate before verifying it.
    pub verify_refusal: Option<Refusal>,
    /// Verus's warnings from its well-formedness check of the function.
    pub warnings: Vec<UserError>,
}

type R<T> = Result<T, FnProblem>;

/// Where code runs; see the module documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ctx {
    Exec,
    Proof,
    Spec,
}

impl Ctx {
    /// Ghost code: proof or spec.
    fn ghost(self) -> bool {
        self != Self::Exec
    }

    /// The mode of a local declared here: exec locals only outside ghost
    /// code; everything else is spec, as a Verus `let` in proof code is.
    fn local_mode(self) -> Mode {
        match self {
            Self::Exec => Mode::Exec,
            Self::Proof | Self::Spec => Mode::Spec,
        }
    }
}

/// Which part of a function is being read. Verus holds a public function's
/// `requires` and `ensures`, and a spec function's body, to the visibility
/// of where they can be seen (`well_formed.rs`, `check_function`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Area {
    Requires,
    Recommends,
    Ensures,
    Returns,
    Decreases,
    When,
    Unwind,
    Body,
}

fn refuse<T>(tag: &'static str, detail: impl Into<String>, span: Span) -> R<T> {
    Err(FnProblem::Refused(Refusal::new(tag, detail, span)))
}

/// A function's outcome for an attribute problem: Verus's error from the
/// phase that builds VIR, or a refusal when the reader does not reproduce
/// what Verus does.
fn attr_problem(problem: &AttrProblem) -> FnProblem {
    match problem {
        AttrProblem::Error(span, message) => {
            FnProblem::Rejected(UserError::new(Phase::RustToVir, *span, message.clone()))
        }
        AttrProblem::Unmodelled(span, detail) => {
            FnProblem::Refused(Refusal::new("attribute", detail.clone(), *span))
        }
    }
}

/// Verus's range check on an integer literal of type `ty`
/// (`rust_to_vir_expr.rs`, `check_lit_int`): `magnitude` must fit the type,
/// one more for a negated literal of a signed type. `usize` and `isize` are
/// checked against the narrowest source-selected width (32 by default).
fn check_lit_int(
    span: Span,
    negative: bool,
    magnitude: u128,
    ty: &Ty,
    architecture: trust_vc_vcir::bitvector::Architecture,
) -> R<()> {
    let Some(range) = ty.int_range() else {
        return refuse("literal", "an integer literal of a non-integer type", span);
    };
    let bump = u128::from(negative);
    let min_width = architecture
        .cases()
        .ok()
        .and_then(|widths| widths.first())
        .copied()
        .ok_or_else(|| {
            FnProblem::Refused(Refusal::new(
                "architecture",
                "an invalid source architecture",
                span,
            ))
        })?;
    let fits = match range {
        IntRange::Int | IntRange::Nat => true,
        IntRange::U(n) => n == 128 || (n < 128 && magnitude < (1u128 << n)),
        IntRange::I(n) => (1..=128).contains(&n) && magnitude < (1u128 << (n - 1)) + bump,
        IntRange::USize => magnitude < (1u128 << min_width),
        IntRange::ISize => magnitude < (1u128 << (min_width - 1)) + bump,
        IntRange::Char => false,
    };
    if fits {
        Ok(())
    } else {
        Err(FnProblem::Rejected(UserError::new(
            Phase::RustToVir,
            span,
            messages::lit_out_of_range(&format!("{range:?}")),
        )))
    }
}

/// Read the generic function `def_id` at the concrete type arguments
/// `args`, as the instance `id` ([`FnRole::Instance`]). Errors Verus reports
/// belong to the generic function and are dropped here.
pub(crate) fn read_instance<'tcx>(
    cx: &Cx<'tcx>,
    def_id: LocalDefId,
    args: ty::GenericArgs<'tcx>,
    id: trust_vc_vcir::FnId,
) -> R<FnDecl> {
    let mut reader = FnReader::build(cx, def_id, Some((args, id)), false)?;
    let mut decl = reader.read()?;
    if let Some(refusal) = reader.verify_refusal.take() {
        return Err(FnProblem::Refused(refusal));
    }
    decl.id = id;
    decl.role = FnRole::Instance;
    decl.type_params = Vec::new();
    let mut type_args = Vec::new();
    for arg in args.iter() {
        match arg.kind() {
            ty::GenericArgKind::Lifetime(_) => {}
            ty::GenericArgKind::Type(t) => {
                let Some(t) = reader.vc_ty(reader.at(t))? else {
                    return refuse(
                        "instance",
                        "an unrepresented native instance type argument",
                        cx.tcx.def_span(def_id),
                    );
                };
                type_args.push(t);
            }
            ty::GenericArgKind::Const(_) => {
                return refuse(
                    "instance",
                    "a const generic instance argument",
                    cx.tcx.def_span(def_id),
                );
            }
        }
    }
    let Some(original) = cx.fns.get(&def_id.to_def_id()) else {
        return refuse(
            "instance",
            "an unregistered native instance declaration",
            cx.tcx.def_span(def_id),
        );
    };
    decl.attrs.instance = Some(trust_vc_vcir::GenericInstance {
        declaration: original.id,
        type_args,
    });
    decl.name = format!("{}::<{args:?}>", decl.name);
    cx.ghost_tail_occurrences
        .borrow_mut()
        .append(&mut reader.ghost_tail_occurrences);
    Ok(decl)
}

/// Read the function `def_id`, which the crate pass registered.
/// `mode_rejected` says the mode checker found an error in it: the function
/// is read only for the errors of earlier phases, and what breaks a mode
/// rule is read past instead of refused.
pub(crate) fn read_fn(cx: &Cx<'_>, def_id: LocalDefId, mode_rejected: bool) -> FnOutcome {
    if cx.constants.mode(def_id) == Some(ConstMode::Dual)
        && cx.tcx.def_kind(def_id) == DefKind::AssocConst
        && cx.tcx.def_kind(cx.tcx.local_parent(def_id)) == DefKind::Trait
        && matches!(
            cx.tcx.hir_node_by_def_id(def_id),
            hir::Node::TraitItem(hir::TraitItem {
                kind: hir::TraitItemKind::Const(_, None),
                ..
            })
        )
    {
        return FnOutcome {
            result: abstract_constant(cx, def_id),
            errors: Vec::new(),
            deferred: None,
            verify_refusal: None,
            warnings: Vec::new(),
        };
    }
    // Verus's first attribute problem in the function ([`attr_walk`]) is
    // raised where the reader meets its expression. A reading that ends
    // without meeting it ends with it instead: completely, or with a
    // refusal, which may stand for code Verus reads without complaint.
    let finding = attr_walk::first_problem(cx, def_id);
    let with_finding = |result: R<FnDecl>| match (&finding, result) {
        (
            Some(finding),
            Ok(_) | Err(FnProblem::Refused(_) | FnProblem::MissingConstantModes(_)),
        ) => Err(attr_problem(&finding.problem)),
        (_, result) => result,
    };
    let mut reader = match FnReader::new(cx, def_id, mode_rejected) {
        Ok(reader) => reader,
        Err(problem) => {
            return FnOutcome {
                result: with_finding(Err(problem)),
                errors: Vec::new(),
                deferred: None,
                verify_refusal: None,
                warnings: Vec::new(),
            }
        }
    };
    reader.attr_finding.clone_from(&finding);
    let result = with_finding(reader.read()).and_then(|declaration| {
        if cx.legacy_functions.contains(&def_id) && !mode_rejected {
            reader.checked_legacy_context()?;
            if !cx.native_ownership.borrow().contains_key(&def_id) {
                return refuse("legacy-erasure", "legacy source requires a complete native erasure/ownership producer; this body is outside the primitive Copy original-MIR lane", cx.tcx.def_span(def_id));
            }
        }
        Ok(declaration)
    });
    if result.is_ok() && !mode_rejected {
        cx.ghost_tail_occurrences
            .borrow_mut()
            .append(&mut reader.ghost_tail_occurrences);
    }
    FnOutcome {
        result,
        errors: reader.errors,
        deferred: reader.deferred,
        verify_refusal: reader.verify_refusal,
        warnings: reader.warnings,
    }
}

/// A real required trait constant has a signature and no body/value equation.
/// The native declaration supplies every binder and its result type. This is
/// not a placeholder for a failed initializer read.
fn abstract_constant(cx: &Cx<'_>, def: LocalDefId) -> R<FnDecl> {
    let tcx = cx.tcx;
    let span = tcx.def_span(def);
    let mut chain = Vec::new();
    let mut generics = Some(tcx.generics_of(def));
    while let Some(g) = generics {
        chain.push(g);
        generics = g.parent.map(|p| tcx.generics_of(p));
    }
    let mut parameters = Vec::new();
    let mut indices = HashMap::new();
    for g in chain.into_iter().rev() {
        for param in &g.own_params {
            match param.kind {
                ty::GenericParamDefKind::Lifetime => {}
                ty::GenericParamDefKind::Type { .. } => {
                    indices.insert(param.index, parameters.len() as u32);
                    parameters.push(param.name.to_string());
                }
                ty::GenericParamDefKind::Const { .. } => {
                    return refuse("generics", "a trait constant with const parameters", span)
                }
            }
        }
    }
    let rustc_ty = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, def.to_def_id()),
            tcx.type_of(def).instantiate_identity(),
        )
        .map_err(|error| {
            FnProblem::Refused(Refusal::new(
                "type",
                format!("a trait constant result that could not be normalized: {error:?}"),
                span,
            ))
        })?;
    if let Some((problem, at)) = cx
        .verus_where_problem(def.to_def_id())
        .map_err(FnProblem::Refused)?
    {
        return refuse(super::TAG_VERUS_TYPE, problem, at);
    }
    if let Some(problem) = cx
        .verus_ty_problem_allowing_mut(rustc_ty, def.to_def_id())
        .map_err(FnProblem::Refused)?
    {
        return refuse(super::TAG_VERUS_TYPE, problem, span);
    }
    let result = cx
        .vc_ty_with(rustc_ty, &|p: ty::ParamTy| indices.get(&p.index).copied())
        .ok_or_else(|| {
            FnProblem::Refused(Refusal::new(
                "type",
                format!("an unsupported trait constant result `{rustc_ty}`"),
                span,
            ))
        })?;
    let attributes = cx.declaration_attrs(def);
    native_constant_attributes(tcx, def)?;
    if attributes.inline
        || attributes.open
        || attributes.closed
        || attributes.opaque
        || attributes.external_body
    {
        return refuse(
            "constant",
            "an unsupported publication attribute on a required trait constant",
            span,
        );
    }
    Ok(FnDecl {
        id: cx.fns[&def.to_def_id()].id,
        name: cx.friendly_fn_path(def.to_def_id()),
        span: cx.span_id(span),
        mode: Mode::Spec,
        role: FnRole::TraitDecl,
        kind: FnKind::Constant(ConstMode::Dual),
        type_params: parameters,
        copy_premises: Vec::new(),
        locals: vec![LocalDecl {
            name: "result".into(),
            ty: result,
            mode: Mode::Exec,
            prophecy: DeclProphecy::Default,
            mutable: false,
            kind: LocalKind::Return,
            span: cx.span_id(span),
        }],
        params: Vec::new(),
        ret: LocalId(0),
        requires: Vec::new(),
        ensures: Vec::new(),
        recommends: Vec::new(),
        unwind: None,
        decreases: Vec::new(),
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::None,
    })
}

/// Keep function-only attributes from acquiring different semantics through
/// the new constant representation. Ordinary Rust attributes remain native.
fn native_constant_attributes(tcx: TyCtxt<'_>, def: LocalDefId) -> R<()> {
    for (attribute, span) in attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(def))) {
        if !matches!(
            attribute,
            VerusAttr::VerusMacro
                | VerusAttr::ExternalBody
                | VerusAttr::Rlimit(_)
                | VerusAttr::SpinoffProver
        ) {
            return refuse(
                "constant-attribute",
                format!("{attribute:?} on a native associated constant"),
                span,
            );
        }
    }
    Ok(())
}

struct FnReader<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    tcx: TyCtxt<'tcx>,
    /// The type-check results of the body being read ([`Self::body_def`]).
    typeck: &'tcx TypeckResults<'tcx>,
    /// The function.
    def_id: LocalDefId,
    /// The item whose body is read: the function itself, or the
    /// specification method (`VERUS_SPEC__f`) of a trait method declaration.
    body_def: LocalDefId,
    checked_modes: Option<std::rc::Rc<super::modes::CheckedModes<'tcx>>>,
    header_binding_scopes: header_binding_scope::Scopes<'a, 'tcx>,
    ghost_tail_occurrences: Vec<super::modes::ExpectedGhostTail>,
    /// Concrete type arguments every type of the body is read at: those of
    /// an instance, or those of an implementation while its trait's
    /// clauses are read.
    subst: Option<ty::GenericArgs<'tcx>>,
    /// What the function stands for.
    role: FnRole,
    /// VcIR type parameters, by name.
    type_params: Vec<String>,
    /// rustc's index of each type parameter in scope, to its VcIR index.
    param_index: HashMap<u32, u32>,
    mode: Mode,
    reading_initializer: bool,
    locals: Vec<LocalDecl>,
    /// Whether each local held a value when declared (parameters, `let`s
    /// with an initializer). Assigning such a local needs `mut`.
    initialized: Vec<bool>,
    local_ids: HashMap<HirId, LocalId>,
    params: Vec<LocalId>,
    ret: LocalId,
    next_site: u32,
    errors: Vec<UserError>,
    /// A refusal that stands unless a Verus error rejects the function
    /// first (for example an unsupported parameter type in a function whose
    /// `requires` Verus rejects).
    pending: Option<Refusal>,
    /// See [`FnOutcome::deferred`].
    deferred: Option<Span>,
    /// See [`FnOutcome::verify_refusal`].
    verify_refusal: Option<Refusal>,
    /// The function's signature, where Verus reports header rules.
    sig_span: Span,
    /// The part of the function being read.
    area: Area,
    /// The `ensures` names the return value (`ensures(|r: T| ..)`); holds
    /// the type the closure gives it.
    ensures_ret_ty: Option<ty::Ty<'tcx>>,
    returns_clause: Option<returns::Value<'tcx>>,
    /// The mode checker rejected the function; see [`read_fn`].
    mode_rejected: bool,
    /// The `hide` calls Verus takes as headers of the function; see
    /// [`Self::leading_hides`].
    header_hides: HashSet<HirId>,
    /// The body's tail expression.
    body_tail: Option<HirId>,
    /// Verus's first attribute problem in the function; see [`read_fn`].
    attr_finding: Option<AttrFinding>,
    /// Reading the clauses a trait implementation method inherits: the
    /// implementations they use are Verus's dependencies of the trait, not
    /// of this function (`cycles`).
    inheriting: bool,
    /// The loop settings the function inherits.
    loop_settings: LoopSettings,
    /// The loops around the expression being read, innermost last.
    loops: Vec<LoopScope>,
    next_loop: u32,
    /// The expression [`Self::expr_adjusted`] reads with its adjustments.
    adjusting: Option<HirId>,
    /// The id of the function being read (or of the instance).
    own_id: trust_vc_vcir::FnId,
    /// The header holds `opens_invariants none`.
    opens_none: bool,
    /// The actual declared or inherited unwind contract.
    unwind: Option<UnwindSpec>,
    /// The header's `decreases` measure.
    decreases: Vec<Expr>,
    /// The header's `decreases_when` condition.
    decreases_when: Option<Expr>,
    /// The header's `decreases_by` (or `recommends_by`) function, with the
    /// header call's span.
    decreases_by: Option<(DefId, Span)>,
    /// The `#[trigger]` marks met while reading the quantifiers being read.
    trigger_marks: Vec<trust_vc_vcir::triggers::Mark>,
    /// The quantifiers being read, innermost last.
    quant_frames: Vec<quant::QuantFrame>,
    /// Original outer hints of a local broadcast proof's complete header.
    broadcast_triggers: Option<Vec<Vec<Expr>>>,
    broadcast_header_active: bool,
    /// Verus's well-formedness warnings found while reading.
    warnings: Vec<UserError>,
}

/// The clauses a trait method implementation inherits from the
/// declaration; see [`FnReader::inherited_clauses`].
#[derive(Default)]
struct Inherited {
    requires: Vec<Clause>,
    ensures: Vec<Clause>,
    recommends: Vec<Clause>,
    unwind: Option<UnwindSpec>,
}

/// What a call runs: see [`FnReader::call_target`].
struct Target {
    id: trust_vc_vcir::FnId,
    mode: Mode,
    ret_mode: Option<Mode>,
    type_args: Vec<Ty>,
}

/// A loop around the expression being read.
struct LoopScope {
    /// The HIR loop, which `break` and `continue` name.
    hir_id: HirId,
    id: LoopId,
    label: Option<rustc_span::Symbol>,
    isolation: bool,
    has_decreases: bool,
}

/// The specification at the head of a loop's body.
struct LoopHeader {
    /// In Verus's order: `invariant_except_break`, `invariant`, `ensures`.
    invariants: Vec<LoopInvariant>,
    decreases: Vec<Expr>,
    /// How many statements it takes.
    len: usize,
}

#[path = "body/constant_values.rs"]
mod constant_values;

impl<'a, 'tcx> FnReader<'a, 'tcx> {
    fn new(cx: &'a Cx<'tcx>, def_id: LocalDefId, mode_rejected: bool) -> R<Self> {
        Self::build(cx, def_id, None, mode_rejected)
    }

    /// A reader of `def_id`, or of its instance at `instance`.
    fn build(
        cx: &'a Cx<'tcx>,
        def_id: LocalDefId,
        instance: Option<(ty::GenericArgs<'tcx>, trust_vc_vcir::FnId)>,
        mode_rejected: bool,
    ) -> R<Self> {
        let tcx = cx.tcx;
        let span = tcx.def_span(def_id);
        let parent = tcx.local_parent(def_id);
        let in_trait = tcx.def_kind(parent) == DefKind::Trait;
        let loose = cx.opts.no_external_by_default;
        if in_trait && !super::is_verus_trait(tcx, parent.to_def_id(), loose) {
            return refuse(
                "trait",
                "a method of a trait the reader does not read",
                span,
            );
        }
        if matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: true })
            && super::trait_impl_problem(tcx, parent, loose).is_some()
            && !cx.derived_clones.admitted(cx, def_id)
        {
            return refuse(
                "trait-impl",
                "a method of a trait implementation the reader does not read",
                span,
            );
        }
        let body_def = if in_trait {
            cx.spec_methods.get(&def_id).copied().unwrap_or(def_id)
        } else {
            def_id
        };
        if tcx.hir_maybe_body_owned_by(body_def).is_none() {
            return refuse("no-body", "a function without a body", span);
        }
        let role = match (instance, in_trait) {
            (Some(_), _) => FnRole::Instance,
            (None, true) => FnRole::TraitDecl,
            (None, false) => FnRole::Item,
        };
        let mode = cx
            .fns
            .get(&def_id.to_def_id())
            .map_or(Mode::Exec, |info| info.mode);
        let typeck = tcx.typeck(body_def);
        // Type parameters, the parents' (a trait's `Self`, an impl's) first.
        let mut type_params = Vec::new();
        let mut param_index = HashMap::new();
        let mut const_param = false;
        if instance.is_none() {
            let mut chain = Vec::new();
            let mut generics = Some(tcx.generics_of(def_id));
            while let Some(g) = generics {
                chain.push(g);
                generics = g.parent.map(|parent| tcx.generics_of(parent));
            }
            for g in chain.into_iter().rev() {
                for param in &g.own_params {
                    match param.kind {
                        ty::GenericParamDefKind::Lifetime => {}
                        ty::GenericParamDefKind::Type { .. } => {
                            let index = u32::try_from(type_params.len()).unwrap_or(u32::MAX);
                            param_index.insert(param.index, index);
                            type_params.push(param.name.to_string());
                        }
                        ty::GenericParamDefKind::Const { .. } => const_param = true,
                    }
                }
            }
        }
        let mut reader = Self {
            cx,
            tcx,
            typeck,
            def_id,
            body_def,
            checked_modes: cx.checked_modes.borrow().get(&def_id).cloned(),
            header_binding_scopes: header_binding_scope::Scopes::default(),
            ghost_tail_occurrences: Vec::new(),
            subst: instance.map(|(args, _)| args),
            role,
            type_params,
            param_index,
            mode,
            reading_initializer: false,
            locals: Vec::new(),
            initialized: Vec::new(),
            local_ids: HashMap::new(),
            params: Vec::new(),
            ret: LocalId(0),
            next_site: 0,
            errors: Vec::new(),
            pending: None,
            deferred: None,
            verify_refusal: None,
            sig_span: tcx
                .hir_node_by_def_id(def_id)
                .fn_sig()
                .map_or(span, |sig| sig.span),
            area: Area::Body,
            ensures_ret_ty: None,
            returns_clause: None,
            mode_rejected,
            header_hides: HashSet::new(),
            body_tail: None,
            attr_finding: None,
            inheriting: false,
            loop_settings: attrs::loop_settings(tcx, def_id.to_def_id()),
            loops: Vec::new(),
            next_loop: 0,
            adjusting: None,
            own_id: instance.map_or_else(
                || {
                    cx.fns.get(&def_id.to_def_id()).map_or_else(
                        || trust_vc_vcir::FnId(cx.def_hash(def_id.to_def_id())),
                        |info| info.id,
                    )
                },
                |(_, id)| id,
            ),
            opens_none: false,
            unwind: None,
            decreases: Vec::new(),
            decreases_when: None,
            decreases_by: None,
            trigger_marks: Vec::new(),
            quant_frames: Vec::new(),
            broadcast_triggers: None,
            broadcast_header_active: false,
            warnings: Vec::new(),
        };
        if const_param {
            reader.pending = Some(Refusal::new(
                "generics",
                "functions with const parameters are not read yet",
                span,
            ));
        }
        // Verus translates the types of the function's bounds with its
        // signature (`check_generics_bounds`).
        if reader.pending.is_none() {
            if let Some((problem, bound_span)) = cx
                .verus_where_problem(def_id.to_def_id())
                .map_err(FnProblem::Refused)?
            {
                reader.pending = Some(Refusal::new(
                    super::TAG_VERUS_TYPE,
                    format!("{problem} in a bound, which Verus does not translate"),
                    bound_span,
                ));
            }
        }
        Ok(reader)
    }

    // ------------------------------------------------------------------
    // Types at the instance's arguments
    // ------------------------------------------------------------------

    /// `t`, from the type-check results, at [`Self::subst`].
    fn at(&self, t: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        let Some(args) = self.subst else {
            if !self.mode_rejected && !self.inheriting
                && t.walk().any(|part| part.as_type().is_some_and(|ty| matches!(ty.kind(), ty::Alias(..))))
                && self.checked_modes.as_ref().is_some_and(|checked|
                    super::projection_types::current(self.cx, self.def_id, self.body_def, self.typeck, checked))
            {
                let uses = super::projection_types::observe_instance(self.cx, self.def_id,
                    self.body_def, self.typeck, self.checked_modes.as_ref(), t);
                self.record_impl_uses(uses.into_iter().map(|implementation| (implementation, true)).collect());
                // The actual occurrence owner's environment, including its
                // original predicates, governs open as well as closed aliases.
                let env = ty::TypingEnv::non_body_analysis(self.tcx, self.body_def.to_def_id());
                if let Ok(normalized) = self.tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new(t)) {
                    if self.checked_modes.as_ref().is_some_and(|checked|
                        super::projection_types::current(self.cx, self.def_id, self.body_def, self.typeck, checked)) {
                        return normalized;
                    }
                }
            }
            return t;
        };
        let tcx = self.tcx;
        let env = ty::TypingEnv::fully_monomorphized();
        let bound = ty::EarlyBinder::bind(tcx, t);
        if !self.mode_rejected && !self.inheriting {
            let uses = super::projection_types::observe_instance(self.cx, self.def_id,
                self.body_def, self.typeck, self.checked_modes.as_ref(),
                bound.instantiate(tcx, args).skip_normalization());
            self.record_impl_uses(uses.into_iter().map(|implementation| (implementation, true)).collect());
        }
        match tcx.try_normalize_erasing_regions(env, bound.instantiate(tcx, args)) {
            Ok(normalized) => {
                let original = bound.instantiate(tcx, args).skip_normalization();
                if original.walk().any(|part| part.as_type().is_some_and(|ty| matches!(ty.kind(), ty::Alias(..))))
                    && !self.checked_modes.as_ref().is_some_and(|checked|
                        super::projection_types::current(self.cx, self.def_id, self.body_def, self.typeck, checked))
                { tcx.erase_and_anonymize_regions(original) } else { normalized }
            }
            Err(_) => {
                tcx.erase_and_anonymize_regions(bound.instantiate(tcx, args).skip_normalization())
            }
        }
    }

    /// Generic arguments from the type-check results, at [`Self::subst`].
    fn at_args(&self, args: ty::GenericArgs<'tcx>) -> ty::GenericArgs<'tcx> {
        let tcx = self.tcx;
        let bound = ty::EarlyBinder::bind(tcx, args);
        let instantiated = self.subst.map_or(args, |subst| bound.instantiate(tcx, subst).skip_normalization());
        let current = !self.mode_rejected && !self.inheriting
            && self.checked_modes.as_ref().is_some_and(|checked|
                super::projection_types::current(self.cx, self.def_id, self.body_def, self.typeck, checked));
        if current {
            for native in instantiated.iter().filter_map(|argument| argument.as_type()) {
                let uses = super::projection_types::observe_instance(self.cx, self.def_id,
                    self.body_def, self.typeck, self.checked_modes.as_ref(), native);
                self.record_impl_uses(uses.into_iter().map(|implementation| (implementation, true)).collect());
            }
        }
        let env = if self.subst.is_some() { ty::TypingEnv::fully_monomorphized() }
            else if current { ty::TypingEnv::non_body_analysis(tcx, self.body_def.to_def_id()) }
            else { return args; };
        match tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new(instantiated)) {
            Ok(normalized) => {
                if instantiated.iter().filter_map(|argument| argument.as_type()).any(|ty|
                    ty.walk().any(|part| part.as_type().is_some_and(|ty| matches!(ty.kind(), ty::Alias(..)))))
                    && !self.checked_modes.as_ref().is_some_and(|checked|
                        super::projection_types::current(self.cx, self.def_id, self.body_def, self.typeck, checked))
                { tcx.erase_and_anonymize_regions(instantiated) } else { normalized }
            }
            Err(_) => tcx.erase_and_anonymize_regions(instantiated),
        }
    }

    fn expr_rty(&self, e: &hir::Expr<'_>) -> ty::Ty<'tcx> {
        self.at(self.typeck.expr_ty(e))
    }

    fn expr_rty_adj(&self, e: &hir::Expr<'_>) -> ty::Ty<'tcx> {
        self.at(self.typeck.expr_ty_adjusted(e))
    }

    fn pat_rty(&self, p: &hir::Pat<'_>) -> ty::Ty<'tcx> {
        self.at(self.typeck.pat_ty(p))
    }

    /// The VcIR type of `t` (already at [`Self::subst`]), with the
    /// function's own type parameters.
    fn vc_ty(&self, t: ty::Ty<'tcx>) -> R<Option<Ty>> {
        if !self.mode_rejected && !self.inheriting {
            let used = super::projection_types::observe_fields(self.cx, self.def_id, self.body_def,
                self.typeck, self.checked_modes.as_ref(), t, &self.cx.projection_type_work).map_err(FnProblem::Refused)?;
            self.record_impl_uses(used.into_iter().map(|implementation| (implementation, true)).collect());
        }
        if t.walk().any(|part| part.as_type().is_some_and(|ty| matches!(ty.kind(), ty::Alias(..))))
            && !self.checked_modes.as_ref().is_some_and(|checked|
                super::projection_types::current(self.cx, self.def_id, self.body_def, self.typeck, checked))
        {
            return refuse("projection-context", "associated types need the current native body and completed modes", self.tcx.def_span(self.def_id));
        }
        if t.walk().any(|part| part.as_type().is_some_and(|ty|
            matches!(ty.kind(), ty::Alias(..)) && !ty.has_param()))
        {
            return refuse("projection-normalization", "a closed associated type has no actual canonical native normalization", self.tcx.def_span(self.def_id));
        }
        let Some(vc) = self.cx.vc_ty_with(t, &|param: ty::ParamTy| {
            self.param_index.get(&param.index).copied()
        }) else {
            return Ok(None);
        };
        // An unsupported value type is still None. A failed native bound
        // query is a refusal and must never become that recoverable case.
        Ok(self
            .cx
            .verus_ty_problem_allowing_mut(t, self.body_def.to_def_id())
            .map_err(FnProblem::Refused)?
            .is_none()
            .then_some(vc))
    }

    // ------------------------------------------------------------------
    // Small helpers
    // ------------------------------------------------------------------

    fn sp(&self, span: Span) -> SpanId {
        self.cx.span_id(span)
    }

    fn site(&mut self) -> SiteId {
        self.next_site += 1;
        SiteId(self.next_site)
    }

    /// Declare a local. `initialized` says whether it holds a value from
    /// its declaration on (parameters, `let`s with an initializer).
    fn add_local(&mut self, decl: LocalDecl, initialized: bool) -> LocalId {
        let id = LocalId(u32::try_from(self.locals.len()).unwrap_or(u32::MAX));
        self.locals.push(decl);
        self.initialized.push(initialized);
        id
    }

    /// A [`LocalDecl`] at a rustc span.
    fn local_decl(
        &self,
        name: &str,
        ty: Ty,
        mode: Mode,
        mutable: bool,
        kind: LocalKind,
        span: Span,
    ) -> LocalDecl {
        LocalDecl {
            name: name.to_string(),
            ty,
            mode,
            prophecy: DeclProphecy::Default,
            mutable,
            kind,
            span: self.sp(span),
        }
    }

    /// A temporary for a flattened value.
    fn temp(&mut self, ty: Ty, ctx: Ctx, span: Span) -> LocalId {
        self.temp_with_mode(ty, ctx.local_mode(), span)
    }

    fn temp_with_mode(&mut self, ty: Ty, mode: Mode, span: Span) -> LocalId {
        let name = format!("tmp%{}", self.locals.len());
        self.add_local(
            self.local_decl(&name, ty, mode, true, LocalKind::Temp, span),
            false,
        )
    }

    /// Record a refusal that stands unless the function is rejected first,
    /// and return a placeholder type so reading can continue.
    fn pending_type(&mut self, what: &str, ty: ty::Ty<'tcx>, span: Span) -> Ty {
        if self.pending.is_none() {
            self.pending = Some(Refusal::new(
                "type",
                format!("{what} has type `{ty}`"),
                span,
            ));
        }
        Ty::Unit
    }

    /// The VcIR type of an expression, or a refusal.
    fn expr_ty(&self, e: &hir::Expr<'_>) -> R<Ty> {
        let ty = self.expr_rty(e);
        match self.vc_ty(ty)? {
            Some(vc) => Ok(vc),
            None => refuse("type", format!("expression of type `{ty}`"), e.span),
        }
    }

    fn unit(&self, span: Span) -> Expr {
        Expr::new(Ty::Unit, self.sp(span), ExprKind::Lit(Lit::Unit))
    }

    fn read_local(&self, local: LocalId, span: Span) -> Expr {
        let ty = self.locals[local.index()].ty.clone();
        Expr::read(Place::local(local), ty, self.sp(span))
    }

    /// The closed original-MIR fragment has only Proof value uses. Keep a
    /// flattened value's actual local mode when saving it before a call;
    /// unrelated Proof code can observe a Proof variable in Spec mode.
    fn operand_mode(&self, value: &Expr, ctx: Ctx) -> Mode {
        if !self.cx.native_ownership.borrow().contains_key(&self.def_id) {
            return ctx.local_mode();
        }
        let ExprKind::Read(place) = &value.kind else {
            return ctx.local_mode();
        };
        if !place.projections.is_empty() {
            return ctx.local_mode();
        }
        self.locals
            .get(place.local.index())
            .map_or(ctx.local_mode(), |local| local.mode)
    }

    /// Lower operands left to right, the order in which Rust evaluates them.
    ///
    /// Lowering an operand can emit statements (an assignment inside a block,
    /// a call). The operands to its left were evaluated before those
    /// statements run, so their values are saved in temporaries placed ahead
    /// of the statements; otherwise `x + { x = 60; y }` would read the new
    /// `x`.
    fn operands(
        &mut self,
        exprs: &[&'tcx hir::Expr<'tcx>],
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Vec<Expr>> {
        let mut values: Vec<Expr> = Vec::new();
        for e in exprs {
            let mark = out.len();
            let value = self.expr_adjusted(e, ctx, out)?;
            if out.len() > mark {
                let mut saves = Vec::new();
                for (prev, source) in values.iter_mut().zip(exprs) {
                    if matches!(prev.kind, ExprKind::Lit(_)) {
                        continue;
                    }
                    let mode = self.legacy_saved_value_mode(source, prev, ctx)?;
                    let t = self.temp_with_mode(prev.ty.clone(), mode, source.span);
                    if self.locals[t.index()].mode == Mode::Spec {
                        // This saves an expression for its later consumer;
                        // it is not an authored Unit declaration, whose mode
                        // check deliberately clears a Unit prophecy effect.
                        self.locals[t.index()].prophecy = DeclProphecy::DelayedInfer;
                    }
                    let declaration =
                        self.legacy_value_declaration(t, prev.clone(), source, ctx, None)?;
                    saves.push(Stmt::new(self.sp(source.span), declaration));
                    *prev = self.read_local(t, source.span);
                }
                out.splice(mark..mark, saves);
            }
            values.push(value);
        }
        Ok(values)
    }

    /// Two operands, left to right (see [`Self::operands`]).
    fn operand_pair(
        &mut self,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<(Expr, Expr)> {
        let mut values = self.operands(&[lhs, rhs], ctx, out)?.into_iter();
        match (values.next(), values.next()) {
            (Some(lv), Some(rv)) => Ok((lv, rv)),
            _ => refuse("expr", "a binary operator without two operands", lhs.span),
        }
    }

    /// `e` as an `int`, by an exact cast unless it already is one.
    fn to_int(&self, e: Expr) -> Expr {
        if e.ty == Ty::int() {
            e
        } else {
            let span = e.span;
            e.cast(CastKind::Exact, Ty::int(), span)
        }
    }

    /// Two integer operands at one type: unchanged when their types agree,
    /// otherwise both as `int` (Verus compares integers as mathematical
    /// values).
    fn unify_ints(&self, a: Expr, b: Expr) -> (Expr, Expr) {
        if a.ty == b.ty {
            (a, b)
        } else {
            (self.to_int(a), self.to_int(b))
        }
    }

    /// The Verus item a resolved callee is, if any.
    fn callee_item(&self, func: &hir::Expr<'_>) -> Option<(VerusItem, DefId)> {
        let def_id = self.callee_def_id(func)?;
        self.cx.verus_item(def_id).map(|item| (item, def_id))
    }

    /// The function a call's callee expression resolves to.
    fn callee_def_id(&self, func: &hir::Expr<'_>) -> Option<DefId> {
        let hir::ExprKind::Path(qpath) = &func.kind else {
            return None;
        };
        match self.typeck.qpath_res(qpath, func.hir_id) {
            Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => Some(def_id),
            _ => None,
        }
    }

    /// Proof notes and custom errors on a clause or assertion argument.
    /// Verus allows one of them in total and reports the second after the
    /// clause's operands ([`attr_walk`]).
    fn clause_attrs(&self, hir_id: HirId) -> R<ClauseAttrs> {
        self.clause_attrs_in(hir_id, self.broadcast_header_active)
    }

    /// [`Self::clause_attrs`] of a clause that is the body of a quantifier
    /// when `in_binder` (the conclusion of `assert forall`): its trigger
    /// annotations belong to that quantifier, which
    /// [`Self::trigger_attrs`] gave them to.
    fn clause_attrs_in(&self, hir_id: HirId, in_binder: bool) -> R<ClauseAttrs> {
        let mut out = ClauseAttrs::default();
        for (attr, span) in attrs::verus_attrs(self.tcx.hir_attrs(hir_id)) {
            match attr {
                VerusAttr::ProofNote(text) => out.proof_notes.push(text),
                VerusAttr::CustomErr(text) => out.custom_errs.push(text),
                VerusAttr::Trigger(_) | VerusAttr::AutoTrigger | VerusAttr::AllTriggers
                    if in_binder => {}
                other => return refuse("attribute", format!("{other:?} on an expression"), span),
            }
        }
        Ok(out)
    }

    /// Raise Verus's attribute problem if it belongs to `e` at this point,
    /// before its operands or after them ([`attr_walk`]).
    fn attr_hook(&self, e: &hir::Expr<'_>, after: bool) -> R<()> {
        match &self.attr_finding {
            Some(finding) if finding.at == e.hir_id && finding.after == after => {
                Err(attr_problem(&finding.problem))
            }
            _ => Ok(()),
        }
    }

    // ------------------------------------------------------------------
    // The function
    // ------------------------------------------------------------------

    fn read(&mut self) -> R<FnDecl> {
        let tcx = self.tcx;
        let def_id = self.def_id;
        let hir_id = tcx.local_def_id_to_hir_id(def_id);
        let span = tcx.def_span(def_id);
        // A trait method declaration's attributes (`open`, `opaque`, ..)
        // are on its specification method.
        let item_attrs = self.cx.declaration_attrs(self.body_def);

        if let Some(decl) = tcx.hir_fn_decl_by_hir_id(hir_id) {
            if decl.implicit_self() == ImplicitSelfKind::Mut {
                return Err(FnProblem::Rejected(UserError::new(
                    Phase::RustToVir,
                    span,
                    messages::unsupported("mut self"),
                )));
            }
        }

        if tcx.def_kind(def_id) == DefKind::AssocConst {
            return self.read_native_constant();
        }
        if matches!(
            self.cx.constants.kind(def_id),
            FnKind::Constant(ConstMode::Exec) | FnKind::Static
        ) && !self.mode_rejected
        {
            self.checked_initializer()?;
        }

        let body_hir = tcx.local_def_id_to_hir_id(self.body_def);
        let sig = self.typeck.liberated_fn_sigs()[body_hir];
        self.verus_item_rules(sig.safety().is_unsafe(), span)?;
        let ret_rustc = self.at(sig.output());
        if self.cx.opts.new_mut_ref
            && self.mode != Mode::Spec
            && ret_rustc.walk().any(|arg| {
                arg.as_type()
                    .is_some_and(|t| matches!(t.kind(), ty::Ref(_, _, m) if m.is_mut()))
            })
        {
            return refuse("new-mut-ref", "an executable or proof return holding `&mut` without native availability and resolution", span);
        }
        let ret_ty = match self.vc_ty(ret_rustc)? {
            Some(ty) => ty,
            None => self.pending_type("the return value", ret_rustc, span),
        };
        let mut ret_mode = self
            .cx
            .native_ownership
            .borrow()
            .get(&self.def_id)
            .map_or_else(
                || {
                    if self.mode == Mode::Exec
                        || self.cx.constants.mode(self.def_id) == Some(ConstMode::Dual)
                    {
                        Mode::Exec
                    } else {
                        Mode::Spec
                    }
                },
                |ownership| ownership.ret_mode(),
            );
        // Upstream uses the function mode for an omitted Unit return type;
        // get_ret_mode's Spec default applies only to a written return type.
        // Explicit tracked results still require the original ownership gate.
        if self.mode == Mode::Proof && ret_ty == Ty::Unit {
            if let Some(checked) = &self.checked_modes {
                if checked.signature.def_id == def_id.to_def_id()
                    && checked.signature.body_owner == self.body_def
                    && matches!(
                        checked.signature.ret.origin,
                        super::modes::ModeOrigin::ImplicitReturn
                    )
                {
                    ret_mode = checked.signature.ret.mode;
                }
            }
        }
        // A tracked result needs the same original-root ownership gate as
        // tracked parameters and local values.
        if let Some(declared) = item_attrs.ret_mode {
            if declared != ret_mode && !self.mode_rejected && self.pending.is_none() {
                self.pending = Some(Refusal::new(
                    "return-mode",
                    format!("a return value of mode {}", declared.name()),
                    span,
                ));
            }
        }
        self.ret = self.add_local(
            self.local_decl(
                "result",
                ret_ty.clone(),
                ret_mode,
                false,
                LocalKind::Return,
                span,
            ),
            false,
        );

        let Some(body) = tcx.hir_maybe_body_owned_by(self.body_def) else {
            return refuse("no-body", "a function without a body", span);
        };
        let default_param_mode = if self.mode == Mode::Exec {
            Mode::Exec
        } else {
            Mode::Spec
        };
        let signature_modes =
            match super::modes::signature_modes(self.cx, self.def_id.to_def_id(), self.sig_span) {
                super::modes::SignatureModeResult::Known(signature)
                    if signature.def_id == self.def_id.to_def_id()
                        && signature.body_owner == self.body_def
                        && signature.mode == self.mode =>
                {
                    Some(signature)
                }
                // Reading a rejected function continues for earlier-phase
                // errors. An unavailable elaboration must not preempt those.
                _ => None,
            };
        for param in body.params {
            let elaborated = signature_modes
                .as_ref()
                .and_then(|signature| signature.params.iter().find(|p| p.hir_id == param.hir_id));
            // A tracked parameter is admitted only in a body whose original
            // compiler MIR checks its exact ownership semantics. The shim
            // must check every such root before publishing any result.
            if let Some((attr, attr_span)) = attrs::verus_attrs(tcx.hir_attrs(param.hir_id))
                .into_iter()
                .next()
            {
                // A function the mode checker rejected is only read for
                // errors of earlier phases, which a parameter's mode does
                // not change.
                let native_tracked = self.cx.native_ownership.borrow().contains_key(&self.def_id)
                    && elaborated.is_some_and(|p| attr == VerusAttr::Mode(p.declared.mode));
                if !native_tracked
                    && !self.mode_rejected
                    && self.cx.legacy_functions.contains(&self.def_id)
                    && matches!(attr, VerusAttr::Mode(_))
                {
                    self.checked_legacy_context()?;
                    return refuse("legacy-erasure", "a legacy parameter requires native erasure/ownership outside the primitive Copy original-MIR lane", param.span);
                }
                if !(native_tracked || self.mode_rejected && matches!(attr, VerusAttr::Mode(_))) {
                    let attr_span = if matches!(attr, VerusAttr::Mode(_)) {
                        elaborated.map_or(attr_span, |p| p.declared.declaration_span(attr_span))
                    } else {
                        attr_span
                    };
                    return refuse("param-mode", format!("{attr:?} on a parameter"), attr_span);
                }
            }
            let param_mode = if self.mode_rejected {
                default_param_mode
            } else {
                elaborated.map_or(default_param_mode, |p| p.declared.mode)
            };
            let PatKind::Binding(BindingMode(ByRef::No, mutability), pat_hir, ident, None) =
                param.pat.kind
            else {
                return refuse(
                    "param-pattern",
                    "a parameter that is not a plain name",
                    param.pat.span,
                );
            };
            let rustc_ty = self.pat_rty(param.pat);
            let has_mut_ref = rustc_ty.walk().any(|arg| {
                arg.as_type()
                    .is_some_and(|t| matches!(t.kind(), ty::Ref(_, _, m) if m.is_mut()))
            });
            if self.cx.opts.new_mut_ref && has_mut_ref && self.mode != Mode::Spec {
                // Pure Spec inputs are immutable logical carrier values.
                // Executable/Proof storage still requires native shadow-read
                // availability and owned-value resolution before admission.
                return refuse(
                    "new-mut-ref",
                    "an executable or proof parameter holding `&mut` without native availability and resolution",
                    param.span,
                );
            }
            if self.mode == Mode::Spec
                && !self.cx.opts.new_mut_ref
                && self.is_mut_ref_param(rustc_ty)
            {
                return Err(FnProblem::Rejected(UserError::new(
                    Phase::RustToVir,
                    param.span,
                    messages::MUT_REF_PARAM_SPEC_FN,
                )));
            }
            let ty = match self.vc_ty(rustc_ty)? {
                Some(ty) => ty,
                None => {
                    self.pending_type(&format!("parameter `{ident}`"), rustc_ty, param.pat.span)
                }
            };
            // The whole parameter, `mut x: T`, which is where Verus reports
            // problems with a parameter.
            let id = self.add_local(
                self.local_decl(
                    ident.name.as_str(),
                    ty,
                    param_mode,
                    mutability.is_mut(),
                    LocalKind::Param,
                    elaborated.map_or(param.span, |p| p.span),
                ),
                true,
            );
            self.local_ids.insert(pat_hir, id);
            self.params.push(id);
        }

        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut recommends = Vec::new();
        // The clauses a trait method implementation inherits.
        let mut inherited: Option<Inherited> = None;

        let bodyless_spec =
            self.mode == Mode::Spec && item_attrs.uninterp && item_attrs.external_body;
        let vc_body = if bodyless_spec {
            // An uninterpreted spec function: the source body is its header
            // clauses and a placeholder the macro emits (`unimplemented!()`).
            // The clauses are read for Verus's header rules.
            if let hir::ExprKind::Block(block, None) = body.value.kind {
                let header_len = self.broadcast_header(
                    block,
                    &mut requires,
                    &mut ensures,
                    &mut recommends,
                    item_attrs.broadcast_forall,
                )?;
                self.termination_rules(&item_attrs, &requires, &ensures);
                self.area = Area::Body;
                self.external_body_headers(&block.stmts[header_len..], block.expr)?;
            }
            Body::None
        } else {
            let hir::ExprKind::Block(block, None) = body.value.kind else {
                return refuse(
                    "expr",
                    "a function body that is not a block",
                    body.value.span,
                );
            };
            let header_len = self.broadcast_header(
                block,
                &mut requires,
                &mut ensures,
                &mut recommends,
                item_attrs.broadcast_forall,
            )?;
            // Verus checks these before the body (`check_function`).
            self.termination_rules(&item_attrs, &requires, &ensures);
            self.area = Area::Body;
            let rest = &block.stmts[header_len..];
            if item_attrs.external_body {
                self.external_body_headers(rest, block.expr)?;
            }
            let implemented_trait_fn = self.implemented_trait_fn();
            if let Some(trait_fn) = implemented_trait_fn {
                self.impl_rules(trait_fn, &requires, &recommends);
            }
            self.decl_rules();
            // Verus builds an `external_body` function's body keeping only
            // its header clauses (`fn_call_to_vir.rs`): a `no_method_body()`
            // call is dropped with the rest, wherever it stands.
            let erased = item_attrs.external_body;
            if !erased
                && rest.iter().any(|s| match s.kind {
                    hir::StmtKind::Semi(e) | hir::StmtKind::Expr(e) => self.is_no_method_body(e),
                    _ => false,
                })
            {
                return refuse(
                    "no-method-body",
                    "no_method_body() after other statements",
                    span,
                );
            }
            let no_method_body = match block.expr {
                Some(tail) if !erased && self.is_no_method_body(tail) => {
                    if !rest.is_empty() {
                        return Err(FnProblem::Rejected(UserError::new(
                            Phase::RustToVir,
                            tail.span,
                            messages::traits::NO_METHOD_BODY_AFTER_STATEMENTS,
                        )));
                    }
                    true
                }
                _ => false,
            };
            // `check_item_fn`: `no_method_body()` belongs in the
            // specification method of a trait method declaration, and a
            // specification method needs it.
            let spec_method = self.body_def != self.def_id;
            let in_trait = tcx.def_kind(tcx.local_parent(def_id)) == DefKind::Trait;
            let spec_sig = super::sig_span(tcx, self.body_def);
            match (in_trait, no_method_body, spec_method) {
                (true, false, true) => {
                    return Err(FnProblem::Rejected(UserError::new(
                        Phase::RustToVir,
                        spec_sig,
                        messages::traits::SPEC_WITHOUT_NO_METHOD_BODY,
                    )))
                }
                (true, true, true) | (_, false, false) => {}
                (_, true, _) | (false, false, true) => {
                    return Err(FnProblem::Rejected(UserError::new(
                        Phase::RustToVir,
                        spec_sig,
                        messages::traits::NO_METHOD_BODY_OUTSIDE_DECL,
                    )))
                }
            }
            // Reject an invalid local body marker before requesting inherited
            // binding facts. That marker can itself prevent a complete native
            // mode walk; it grants no permission to read an inherited header.
            if let Some(trait_fn) = implemented_trait_fn {
                inherited = Some(self.inherited_clauses(trait_fn)?);
            }
            self.header_hides = self.leading_hides(rest)?;
            self.body_tail = block.expr.map(|tail| tail.hir_id);
            if item_attrs.external_body || no_method_body {
                Body::None
            } else {
                match self.mode {
                    Mode::Spec if self.cx.constants.mode(def_id) == Some(ConstMode::Dual) => {
                        Body::Constant(self.initializer_block(rest, block.expr, block.span)?)
                    }
                    Mode::Spec => self.spec_fn_body(rest, block.expr, block.span)?,
                    Mode::Exec => Body::Stmts(self.stmt_body(rest, block, Ctx::Exec, &ret_ty)?),
                    Mode::Proof => Body::Stmts(self.stmt_body(rest, block, Ctx::Proof, &ret_ty)?),
                }
            }
        };
        if self.body_def != def_id {
            self.spec_method_rules(&sig)?;
        }

        // Verus's attribute problem in an expression the reader did not
        // meet (a body it does not read, a callee it resolves by name): Verus
        // meets it while building the body's VIR.
        if let Some(finding) = &self.attr_finding {
            return Err(attr_problem(&finding.problem));
        }

        // Verus checks these after building the body's VIR, so errors in the
        // body come first; they reject the function whatever else was not
        // read. An attribute the reader does not know (and refuses) can send
        // Verus down another path (an encoded `const` skips them all), so
        // they are only checked without one.
        if item_attrs.unsupported.is_empty() {
            if matches!(
                self.cx.constants.kind(def_id),
                FnKind::Constant(_) | FnKind::Static
            ) {
                let executable = matches!(
                    self.cx.constants.kind(def_id),
                    FnKind::Constant(ConstMode::Exec) | FnKind::Static
                );
                let error = if !requires.is_empty() || !recommends.is_empty() {
                    Some("consts cannot have requires/recommends")
                } else if !executable && !ensures.is_empty() {
                    Some("const cannot have `ensures` unless it is `exec const`")
                } else {
                    None
                };
                if let Some(message) = error {
                    return Err(FnProblem::Rejected(UserError::new(
                        Phase::RustToVir,
                        span,
                        message,
                    )));
                }
            } else {
                self.header_rules(&requires, &ensures, &recommends, ret_rustc)?;
            }
            self.trait_publish_rules(&item_attrs, &vc_body)?;
            self.publish_rules(&item_attrs, !matches!(vc_body, Body::None))?;
            if item_attrs.inline {
                let problem = if self.mode != Mode::Spec {
                    Some("'inline' is only allowed for 'spec' functions")
                } else if !item_attrs.open && self.fn_visibility() != self.own_module() {
                    Some("'inline' is only allowed for private or 'open spec' functions")
                } else if !self.decreases.is_empty() {
                    Some("'inline' functions cannot be recursive")
                } else if !matches!(vc_body, Body::Spec(_)) {
                    Some("'inline' functions must have a body")
                } else {
                    None
                };
                if let Some(message) = problem {
                    self.errors
                        .push(UserError::new(Phase::WellFormed, self.sig_span, message));
                }
            }
        }
        self.finish_returns_clause(&mut ensures, ret_rustc)?;
        self.derived_clone_ensures(&mut ensures, span)?;
        self.drop_rules(&requires);
        self.unwind_rules();
        self.invariant_mask(&vc_body)?;

        if item_attrs.broadcast_forall {
            self.broadcast_rules(span)?;
        }

        if let Some(refusal) = self.pending.take() {
            return Err(FnProblem::Refused(refusal));
        }
        let decreases_by = match self.decreases_by {
            None => None,
            Some((target, at)) => match self.cx.fns.get(&target) {
                Some(info) => Some(info.id),
                None => {
                    return refuse(
                        "decreases-by",
                        "a decreases_by function that is not a function of this crate",
                        at,
                    )
                }
            },
        };
        // Inherited clauses come before the function's own
        // (`vir/src/ast_to_sst_func.rs`, `func_body_to_sst`).
        if let Some(mut inherited) = inherited {
            self.cx.inherited_counts.borrow_mut().insert(
                self.own_id,
                (
                    inherited.requires.len(),
                    inherited.ensures.len(),
                    inherited.recommends.len(),
                    inherited.unwind.is_some(),
                ),
            );
            inherited.requires.append(&mut requires);
            requires = inherited.requires;
            inherited.ensures.append(&mut ensures);
            ensures = inherited.ensures;
            inherited.recommends.append(&mut recommends);
            recommends = inherited.recommends;
            self.unwind = inherited.unwind;
        }
        // A body Verus shows only inside part of the crate is hidden from
        // the functions outside it (`module_hidden_definitions`), except for
        // trait methods and bodies opened to a path, which are refused.
        let in_trait = tcx.def_kind(tcx.local_parent(def_id)) == DefKind::Trait
            || tcx.trait_impl_of_assoc(def_id.to_def_id()).is_some();
        if matches!(vc_body, Body::Spec(_))
            && !self.body_visible_crate_wide(item_attrs.open)
            && (in_trait || super::has_open_qualifier(tcx, def_id))
            && self.verify_refusal.is_none()
        {
            self.verify_refusal = Some(Refusal::new(
                "module-visibility",
                "a spec function body that Verus shows only inside its module",
                span,
            ));
        }
        let copy_premises = self.native_copy_premises()?;
        Ok(FnDecl {
            id: self
                .cx
                .fns
                .get(&def_id.to_def_id())
                .map(|info| info.id)
                .unwrap_or(trust_vc_vcir::FnId(self.cx.def_hash(def_id.to_def_id()))),
            name: self.cx.friendly_fn_path(def_id.to_def_id()),
            span: self.sp(span),
            mode: self.mode,
            role: self.role,
            kind: self.cx.constants.kind(def_id),
            type_params: std::mem::take(&mut self.type_params),
            copy_premises,
            locals: std::mem::take(&mut self.locals),
            params: std::mem::take(&mut self.params),
            ret: self.ret,
            requires,
            ensures,
            recommends,
            unwind: self.unwind.take(),
            decreases: std::mem::take(&mut self.decreases),
            decreases_when: self.decreases_when.take(),
            decreases_by,
            attrs: FnAttrs {
                bitvector_scalar_inputs: true,
                inline: item_attrs.inline,
                prophetic: item_attrs.prophetic,
                opaque: item_attrs.opaque,
                external_body: item_attrs.external_body,
                broadcast_triggers: self.broadcast_triggers.take(),
                rlimit: item_attrs.rlimit,
                exec_allows_no_decreases: self.loop_settings.allow_no_decreases
                    || item_attrs.assume_termination,
                is_decreases_by: item_attrs.decreases_by,
                is_trait_method_impl: self
                    .tcx
                    .trait_impl_of_assoc(self.def_id.to_def_id())
                    .is_some(),
                instance: None,
            },
            body: vc_body,
        })
    }

    /// `check_function`'s rules on `decreases`, `when` and `decreases_by`,
    /// in Verus's order, reported at the function.
    fn termination_rules(
        &mut self,
        item_attrs: &attrs::ItemAttrs,
        requires: &[Clause],
        ensures: &[Clause],
    ) {
        use messages::termination as msg;
        let tcx = self.tcx;
        let span = tcx.def_span(self.def_id);
        let in_trait = tcx.def_kind(tcx.local_parent(self.def_id)) == DefKind::Trait
            || tcx.trait_impl_of_assoc(self.def_id.to_def_id()).is_some();
        let mut found: Option<&str> = None;
        if item_attrs.decreases_by {
            let ret_unit = self
                .locals
                .get(self.ret.index())
                .is_none_or(|ret| ret.ty == Ty::Unit);
            found = if in_trait {
                Some(msg::BY_TRAIT_METHOD)
            } else if self.mode != Mode::Proof {
                Some(msg::BY_NOT_PROOF)
            } else if !self.decreases.is_empty() {
                Some(msg::BY_HAS_DECREASES)
            } else if !requires.is_empty() {
                Some(msg::BY_HAS_REQUIRES)
            } else if !ensures.is_empty() {
                Some(msg::BY_HAS_ENSURES)
            } else if !ret_unit {
                Some(msg::BY_HAS_RETURN)
            } else {
                None
            };
        }
        if found.is_none() && self.decreases_by.is_some() && self.mode != Mode::Spec {
            found = Some(msg::BY_NOT_SPEC);
        }
        if found.is_none() && self.decreases_when.is_some() {
            if self.mode != Mode::Spec {
                found = Some(msg::WHEN_NOT_SPEC);
            } else if self.decreases.is_empty() {
                found = Some(msg::WHEN_WITHOUT_DECREASES);
            }
        }
        if let Some(message) = found {
            self.errors
                .push(UserError::new(Phase::WellFormed, span, message));
        }
    }

    /// Item-level rules checked before the parameters: an unsafe function is
    /// refused; a function named `main` that is not exec is Verus's
    /// well-formedness error (checked before the function's clauses). Verus
    /// looks only at the last segment of the path (`ast_util.rs`,
    /// `is_main`), so a `main` in a module or an impl counts too.
    fn verus_item_rules(&mut self, is_unsafe: bool, span: Span) -> R<()> {
        let tcx = self.tcx;
        if is_unsafe {
            return refuse("unsafe", "an unsafe function", span);
        }
        if self.mode != Mode::Exec && tcx.item_name(self.def_id.to_def_id()).as_str() == "main" {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                span,
                messages::wf::MAIN_NOT_EXEC,
            ));
        }
        Ok(())
    }

    /// A rejection at the signature, from the phase that builds VIR.
    fn reject_at_sig<T>(&self, message: &str) -> R<T> {
        Err(FnProblem::Rejected(UserError::new(
            Phase::RustToVir,
            self.sig_span,
            message,
        )))
    }

    /// Verus's header rules (`rust_to_vir_func.rs`, `check_item_fn`, after
    /// the body is built), in Verus's order.
    fn header_rules(
        &self,
        requires: &[Clause],
        ensures: &[Clause],
        recommends: &[Clause],
        ret_rustc: ty::Ty<'tcx>,
    ) -> R<()> {
        use messages::header;
        if self.mode == Mode::Spec && !(requires.is_empty() && ensures.is_empty()) {
            return self.reject_at_sig(header::SPEC_REQUIRES_ENSURES);
        }
        if self.mode == Mode::Spec && self.returns_clause.is_some() {
            return self.reject_at_sig(header::SPEC_RETURNS);
        }
        if self.mode != Mode::Spec && !recommends.is_empty() {
            return self.reject_at_sig(header::NON_SPEC_RECOMMENDS);
        }
        if ensures.is_empty() {
            return Ok(());
        }
        let hir_id = self.tcx.local_def_id_to_hir_id(self.def_id);
        let written_return = self
            .tcx
            .hir_fn_decl_by_hir_id(hir_id)
            .is_some_and(|decl| matches!(decl.output, hir::FnRetTy::Return(_)));
        match (self.ensures_ret_ty, written_return) {
            (None, true) => self.reject_at_sig(header::UNNAMED_RETURN),
            (Some(_), false) => self.reject_at_sig(header::NAMED_DEFAULT_RETURN),
            // Verus compares the two as VIR types and reports a mismatch
            // with VIR's spelling of both, which the reader cannot give.
            (Some(named), true) if named != ret_rustc => refuse(
                "header-shape",
                format!("the ensures return type `{named}` is not the function's `{ret_rustc}`"),
                self.sig_span,
            ),
            _ => Ok(()),
        }
    }

    /// Verus's body visibility and opacity rules (`rust_to_vir_func.rs`,
    /// `get_body_visibility_and_fuel`), checked after the header rules.
    /// `has_body` says the function has a body Verus keeps.
    fn publish_rules(&self, item_attrs: &attrs::ItemAttrs, has_body: bool) -> R<()> {
        use messages::publish;
        if self.mode != Mode::Spec {
            if item_attrs.open {
                return self.reject_at_sig(publish::OPEN_NOT_SPEC);
            }
            if item_attrs.closed {
                return self.reject_at_sig(publish::CLOSED_NOT_SPEC);
            }
            if item_attrs.opaque {
                return self.reject_at_sig(publish::OPAQUE_NOT_SPEC);
            }
            return Ok(());
        }
        // Verus drops the body of an `external_body` function; `verus!`
        // marks a bodyless `uninterp` function `external_body` too. A trait
        // method declaration has none either.
        if item_attrs.external_body || !has_body {
            if item_attrs.opaque {
                return self.reject_at_sig(publish::OPAQUE_WITHOUT_BODY);
            }
            return Ok(());
        }
        if item_attrs.uninterp {
            return self.reject_at_sig(publish::UNINTERP_WITH_BODY);
        }
        if item_attrs.open && self.fn_visibility() == self.own_module() {
            return self.reject_at_sig(publish::OPEN_NOT_PUB);
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Visibility (well_formed.rs)
    // ------------------------------------------------------------------

    /// The function's visibility.
    fn fn_visibility(&self) -> ty::Visibility<ModId> {
        self.tcx.visibility(self.def_id.to_def_id())
    }

    /// Visible in the function's own module: Verus's `private_vis`.
    fn own_module(&self) -> ty::Visibility<ModId> {
        ty::Visibility::Restricted(self.tcx.parent_module_from_def_id(self.def_id).to_mod_id())
    }

    /// Where what is being read must be well formed, with Verus's reason,
    /// when that is wider than the function's module
    /// (`check_function`'s `disallow_private_access`).
    fn required_area(&self) -> Option<(ty::Visibility<ModId>, &'static str)> {
        use messages::wf;
        match self.area {
            Area::Requires | Area::Recommends | Area::Returns => {
                Some((self.fn_visibility(), wf::REASON_REQUIRES))
            }
            Area::Ensures => Some((self.fn_visibility(), wf::REASON_ENSURES)),
            Area::Decreases => Some((self.fn_visibility(), wf::REASON_DECREASES)),
            Area::When => Some((self.fn_visibility(), wf::REASON_WHEN)),
            Area::Unwind => Some((self.fn_visibility(), "unwind clause of public function")),
            Area::Body if self.mode == Mode::Spec => {
                let hir_id = self.tcx.local_def_id_to_hir_id(self.def_id);
                let body = if attrs::item_attrs(self.tcx.hir_attrs(hir_id)).open
                    || self.tcx.def_kind(self.def_id) == DefKind::AssocConst
                {
                    self.fn_visibility()
                } else {
                    self.own_module()
                };
                Some((body, wf::REASON_OPEN_SPEC))
            }
            Area::Body => None,
        }
    }

    /// `check_path_and_get_function`: a function or constant referred to
    /// where it may be less visible than the area requires.
    fn check_function_access(&mut self, callee: DefId, span: Span) {
        let Some((required, reason)) = self.required_area() else {
            return;
        };
        if !covers(self.tcx, self.tcx.visibility(callee), required) {
            // Spec constants can reach this path through their checked native
            // function proxies. Their spelling is not a classification rule.
            let kind = if matches!(
                self.tcx.def_kind(callee),
                DefKind::Const | DefKind::AssocConst
            ) || callee
                .as_local()
                .is_some_and(|local| self.cx.constants.mode(local).is_some())
            {
                "const"
            } else {
                "function"
            };
            self.errors.push(UserError::new(
                Phase::WellFormed,
                span,
                messages::wf::private_reference(reason, kind),
            ));
        }
    }

    /// Verus's name for the module a restricted visibility reaches.
    fn visibility_module(&self, vis: ty::Visibility<ModId>) -> String {
        match vis {
            ty::Visibility::Public => String::new(),
            ty::Visibility::Restricted(module) => self.cx.friendly_path(module.to_def_id()),
        }
    }

    /// `check_datatype_access`: a field expression or constructor (`access`)
    /// of the struct `adt`, which must be visible, and have every field
    /// visible, wherever the area requires (the function's module outside
    /// the areas of [`Self::required_area`]).
    fn check_datatype_access(&mut self, adt: ty::AdtDef<'tcx>, span: Span, access: &str) {
        use messages::wf;
        let tcx = self.tcx;
        let Some(local) = adt.did().as_local() else {
            return;
        };
        let (required, reason) = match self.required_area() {
            Some((vis, reason)) => (vis, Some(reason)),
            None => (self.own_module(), None),
        };
        let dt_vis = tcx.visibility(adt.did());
        // Verus's transparency: the most restrictive of the datatype's and
        // its fields' visibilities. They all reach the datatype's module, so
        // any two are nested.
        let mut transparency = dt_vis;
        for field in adt.all_fields() {
            if covers(tcx, transparency, field.vis) {
                transparency = field.vis;
            }
        }
        let (vis, (message, label), secondary) = if !covers(tcx, dt_vis, required) {
            let module = self.visibility_module(dt_vis);
            (
                dt_vis,
                wf::non_visible_datatype(access),
                wf::only_visible_to(&module),
            )
        } else if !covers(tcx, transparency, required) {
            let module = self.visibility_module(transparency);
            (
                transparency,
                wf::opaque_datatype(access),
                wf::opaque_outside(&module),
            )
        } else {
            return;
        };
        let mut error = UserError::new(Phase::WellFormed, span, message);
        error.primary_label = Some(label);
        error.labels.push((tcx.source_span(local), secondary));
        if let Some(reason) = reason {
            let required_text = match required {
                ty::Visibility::Public => "everywhere".to_string(),
                ty::Visibility::Restricted(module) if module.is_crate_root() => format!(
                    "everywhere in the crate `{}`",
                    self.cx.friendly_path(module.to_def_id())
                ),
                ty::Visibility::Restricted(module) => format!(
                    "everywhere in the module `{}`",
                    self.cx.friendly_path(module.to_def_id())
                ),
            };
            error.help = Some(wf::access_help(
                reason,
                access,
                &required_text,
                &self.visibility_module(vis),
            ));
        }
        self.errors.push(error);
    }

    /// Is this spec function's body visible to every function of the crate?
    /// Verus shows a body only where the function's body visibility reaches:
    /// the function's own module (and its children) for a private or
    /// `closed` function, the function's visibility for an `open` one. The
    /// VC generator has no notion of modules and uses every visible body
    /// everywhere, so only bodies that reach the whole crate are read.
    fn body_visible_crate_wide(&self, open: bool) -> bool {
        use rustc_hir::def_id::{CRATE_DEF_ID, CRATE_MOD_ID};
        let module = self.tcx.parent_module_from_def_id(self.def_id);
        if module.to_local_def_id() == CRATE_DEF_ID {
            return true;
        }
        let visibility = self.tcx.visibility(self.def_id.to_def_id());
        open && (visibility.is_public()
            || visibility == ty::Visibility::Restricted(CRATE_MOD_ID.to_mod_id()))
    }

    /// Is a parameter of this type a `&mut` parameter in Verus's sense
    /// (`rust_to_vir_func.rs`, `is_mut_ty`): `&mut T`, `Ghost<&mut T>` or
    /// `Tracked<&mut T>`?
    fn is_mut_ref_param(&self, ty: ty::Ty<'tcx>) -> bool {
        match ty.kind() {
            ty::Ref(_, _, mutability) => mutability.is_mut(),
            ty::Adt(adt, args)
                if matches!(
                    self.cx.verus_item(adt.did()),
                    Some(VerusItem::Ghost | VerusItem::Tracked)
                ) =>
            {
                args.types()
                    .next()
                    .is_some_and(|inner| matches!(inner.kind(), ty::Ref(_, _, m) if m.is_mut()))
            }
            _ => false,
        }
    }

    /// Is `e` the `no_method_body()` marker of a trait method declaration?
    fn is_no_method_body(&self, e: &hir::Expr<'_>) -> bool {
        match e.kind {
            hir::ExprKind::Call(func, _) => {
                matches!(self.callee_item(func), Some((VerusItem::NoMethodBody, _)))
            }
            _ => false,
        }
    }

    // ------------------------------------------------------------------
    // Traits
    // ------------------------------------------------------------------

    /// The trait method this function implements, when it is a method of a
    /// trait implementation.
    fn implemented_trait_fn(&self) -> Option<LocalDefId> {
        self.tcx.trait_impl_of_assoc(self.def_id.to_def_id())?;
        self.tcx
            .associated_item(self.def_id)
            .trait_item_def_id()?
            .as_local()
    }

    /// The `requires`, `ensures` and `recommends` a method implementing the
    /// trait method `trait_fn` inherits (`vir/src/ast_to_sst_func.rs`,
    /// `Lowerer::inheritance`): the declaration's clauses, with the trait's
    /// `Self` the implementing type and its parameters this function's.
    /// They come before the function's own. Errors in them are the
    /// declaration's, reported where it is read.
    /// Record the implementations a call uses (`bound_impls`) for the cycle
    /// check; `exact` when Verus's graph has the dependency as well.
    fn record_impl_uses(&self, uses: Vec<(LocalDefId, bool)>) {
        if uses.is_empty() {
            return;
        }
        let mut all = self.cx.impl_uses.borrow_mut();
        let entry = all.entry(self.own_id).or_default();
        for (imp, exact) in uses {
            let exact = exact && !self.inheriting;
            *entry.entry(super::cycles::Item(imp)).or_insert(exact) |= exact;
        }
    }

    fn inherited_clauses(&mut self, trait_fn: LocalDefId) -> R<Inherited> {
        let tcx = self.tcx;
        let mut out = Inherited::default();
        let source = self
            .cx
            .spec_methods
            .get(&trait_fn)
            .copied()
            .unwrap_or(trait_fn);
        let Some(body) = tcx.hir_maybe_body_owned_by(source) else {
            return Ok(out);
        };
        let hir::ExprKind::Block(block, None) = body.value.kind else {
            return refuse(
                "trait",
                "a trait method body that is not a block",
                body.value.span,
            );
        };
        if body.params.len() != self.params.len() {
            return refuse(
                "trait",
                "a trait method with another number of parameters",
                self.sig_span,
            );
        }
        let Some(impl_id) = tcx.trait_impl_of_assoc(self.def_id.to_def_id()) else {
            return Ok(out);
        };
        // The declaration's generic arguments: the trait's (from the
        // implementation's trait reference) and the method's own (this
        // function's, or the instance's).
        let own = self
            .subst
            .unwrap_or_else(|| ty::GenericArgs::identity_for_item(tcx, self.def_id));
        let impl_count = tcx.generics_of(impl_id).count();
        if own.len() < impl_count {
            return refuse(
                "generics",
                "a trait implementation method's arguments",
                self.sig_span,
            );
        }
        let trait_args = tcx
            .impl_trait_ref(impl_id)
            .instantiate(tcx, &own.as_slice()[..impl_count])
            .skip_normalization()
            .args;
        let args = tcx.mk_args_from_iter(
            trait_args
                .iter()
                .chain(own.as_slice()[impl_count..].iter().copied()),
        );
        if tcx.generics_of(source).count() != args.len() {
            return refuse(
                "generics",
                "a trait method implemented with other generic parameters",
                self.sig_span,
            );
        }
        for (param, local) in body.params.iter().zip(self.params.clone()) {
            let PatKind::Binding(_, pat_hir, _, None) = param.pat.kind else {
                return refuse(
                    "param-pattern",
                    "a trait method parameter that is not a plain name",
                    param.pat.span,
                );
            };
            self.local_ids.insert(pat_hir, local);
        }
        let binding_scope = if self.mode_rejected {
            // Earlier-phase diagnostics never grant verification permission.
            None
        } else {
            Some(header_binding_scope::Source::for_inherited(
                self, trait_fn, source, body,
            )?)
        };
        let binding_guard = binding_scope
            .map(|scope| self.header_binding_scopes.enter(scope))
            .transpose()?;
        let saved_typeck = std::mem::replace(&mut self.typeck, tcx.typeck(source));
        let saved_subst = self.subst.replace(args);
        let saved_ret_ty = self.ensures_ret_ty.take();
        let saved_ret_name = self.locals[self.ret.index()].name.clone();
        let saved_area = self.area;
        let saved_errors = self.errors.len();
        let saved_finding = self.attr_finding.take();
        let saved_inheriting = std::mem::replace(&mut self.inheriting, true);
        let saved_unwind = self.unwind.take();
        #[cfg(test)]
        header_binding_scope::inspect(self);
        let result = self.header(
            block,
            &mut out.requires,
            &mut out.ensures,
            &mut out.recommends,
        );
        drop(binding_guard);
        out.unwind = self.unwind.take();
        self.unwind = saved_unwind;
        self.typeck = saved_typeck;
        self.subst = saved_subst;
        self.ensures_ret_ty = saved_ret_ty;
        self.locals[self.ret.index()].name = saved_ret_name;
        self.area = saved_area;
        self.errors.truncate(saved_errors);
        self.attr_finding = saved_finding;
        self.inheriting = saved_inheriting;
        match result {
            Ok(_) => Ok(out),
            // The declaration's own reading reports Verus's error; the
            // implementation cannot be verified without its clauses.
            Err(FnProblem::Rejected(error)) => {
                if self.verify_refusal.is_none() {
                    self.verify_refusal = Some(Refusal::new(
                        "trait",
                        format!("the trait method's clauses: {}", error.message),
                        self.sig_span,
                    ));
                }
                Ok(Inherited::default())
            }
            Err(problem) => Err(problem),
        }
    }

    /// `vir/src/well_formed.rs`, `check_function`: a method implementing a
    /// trait method declares no `requires`, no `opens_invariants` and no
    /// unwind specification (all inherited), and the declaration is not
    /// `uninterp`. A spec function's `recommends` are its `requires` there
    /// (`rust_to_vir_func.rs`, `check_item_fn`).
    fn impl_rules(&mut self, trait_fn: LocalDefId, requires: &[Clause], recommends: &[Clause]) {
        use messages::traits;
        let tcx = self.tcx;
        let decl_attrs =
            |def: LocalDefId| attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(def)));
        let spec = self
            .cx
            .spec_methods
            .get(&trait_fn)
            .copied()
            .unwrap_or(trait_fn);
        let message = if !requires.is_empty() || (self.mode == Mode::Spec && !recommends.is_empty())
        {
            traits::IMPL_REQUIRES
        } else if self.opens_none {
            traits::IMPL_OPENS_INVARIANTS
        } else if self.unwind.is_some() {
            traits::IMPL_UNWIND
        } else if decl_attrs(trait_fn).uninterp || decl_attrs(spec).uninterp {
            traits::IMPL_UNINTERP
        } else {
            return;
        };
        self.errors
            .push(UserError::new(Phase::WellFormed, self.sig_span, message));
    }

    /// `check_function`: a trait method declaration without a default body
    /// cannot allow exec code without `decreases`.
    fn decl_rules(&mut self) {
        let tcx = self.tcx;
        if self.role != FnRole::TraitDecl || self.body_def == self.def_id {
            return;
        }
        let allows = [self.def_id, self.body_def].iter().any(|def| {
            attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(*def)))
                .iter()
                .any(|(attr, _)| *attr == VerusAttr::ExecAllowsNoDecreasesClause)
        });
        if allows {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                self.sig_span,
                messages::traits::DECL_NO_DECREASES_ALLOWED,
            ));
        }
    }

    /// `vir/src/traits.rs`, `demote_external_traits`: a method of an
    /// implementation of `Drop` has no `requires`, opens no invariant and
    /// does not unwind; like every method of an implementation of a trait
    /// of another crate, it is exec code.
    fn drop_rules(&mut self, requires: &[Clause]) {
        let tcx = self.tcx;
        let Some(impl_id) = tcx.trait_impl_of_assoc(self.def_id.to_def_id()) else {
            return;
        };
        let trait_id = tcx.impl_trait_id(impl_id);
        if Some(trait_id) != tcx.lang_items().drop_trait() {
            return;
        }
        let message = if !requires.is_empty() {
            messages::traits::DROP_REQUIRES
        } else if !self.opens_none {
            messages::traits::DROP_OPENS_INVARIANTS
        } else if !matches!(self.unwind, Some(UnwindSpec::NoUnwind)) {
            messages::traits::DROP_NO_UNWIND
        } else if self.mode != Mode::Exec {
            messages::traits::EXTERNAL_TRAIT_MODE
        } else {
            return;
        };
        self.errors
            .push(UserError::new(Phase::WellFormed, self.sig_span, message));
    }

    /// The closed invariant-mask fragment remains separate from the typed
    /// unwind contract. Calls still require invariant-opening semantics.
    fn invariant_mask(&self, body: &Body) -> R<()> {
        if !self.opens_none {
            return Ok(());
        }
        let tcx = self.tcx;
        let span = self.sig_span;
        if self.mode != Mode::Exec {
            return refuse(
                "header",
                "opens_invariants on a function that is not exec",
                span,
            );
        }
        let in_trait = tcx.def_kind(tcx.local_parent(self.def_id)) == DefKind::Trait;
        if in_trait {
            return refuse(
                "header",
                "opens_invariants on a trait method declaration",
                span,
            );
        }
        // An implementation of a trait of this crate cannot declare them:
        // [`Self::impl_rules`] reports Verus's error.
        if self.implemented_trait_fn().is_some() {
            return Ok(());
        }
        if let Body::Stmts(block) = body {
            if trust_vc_vcir::vcgen::calls_anything(block) {
                return refuse(
                    "header",
                    "a call in a function marked opens_invariants none",
                    span,
                );
            }
        }
        Ok(())
    }

    /// `make_trait_decl` (`vir/src/headers.rs`): a specification method
    /// has the parameters and the return type of the method it specifies.
    fn spec_method_rules(&self, spec_sig: &ty::FnSig<'tcx>) -> R<()> {
        use messages::traits;
        let tcx = self.tcx;
        let decl_sig = tcx.liberate_late_bound_regions(
            self.def_id.to_def_id(),
            tcx.fn_sig(self.def_id)
                .instantiate_identity()
                .skip_normalization(),
        );
        let reject = |message: &str| {
            Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                super::sig_span(tcx, self.body_def),
                message,
            )))
        };
        let erase = |t: ty::Ty<'tcx>| tcx.erase_and_anonymize_regions(t);
        let type_params = |def: LocalDefId| -> Vec<rustc_span::Symbol> {
            tcx.generics_of(def)
                .own_params
                .iter()
                .filter(|p| !matches!(p.kind, ty::GenericParamDefKind::Lifetime))
                .map(|p| p.name)
                .collect()
        };
        let (decl_params, spec_params) = (type_params(self.def_id), type_params(self.body_def));
        if decl_params.len() != spec_params.len() {
            return reject(traits::SPEC_TYPE_PARAM_COUNT);
        }
        if decl_params != spec_params {
            return reject(traits::SPEC_TYPE_PARAMS);
        }
        if decl_sig.inputs().len() != spec_sig.inputs().len() {
            return reject(traits::SPEC_PARAM_COUNT);
        }
        for (a, b) in decl_sig.inputs().iter().zip(spec_sig.inputs()) {
            if erase(*a) != erase(*b) {
                return reject(traits::SPEC_PARAMS);
            }
        }
        if erase(decl_sig.output()) != erase(spec_sig.output()) {
            return reject(traits::SPEC_RETURN);
        }
        Ok(())
    }

    /// `check_item_fn`'s rules on `open` and `closed` for trait methods: a
    /// declaration without a body cannot have them, and a spec method with
    /// a body (a default method, or an implementation) visible outside its
    /// module needs one.
    fn trait_publish_rules(&self, item_attrs: &attrs::ItemAttrs, body: &Body) -> R<()> {
        use messages::traits;
        let tcx = self.tcx;
        let in_trait = tcx.def_kind(tcx.local_parent(self.def_id)) == DefKind::Trait;
        let trait_impl = tcx.trait_impl_of_assoc(self.def_id.to_def_id()).is_some();
        if !(in_trait || trait_impl) || self.mode != Mode::Spec {
            return Ok(());
        }
        let open_closed = item_attrs.open || item_attrs.closed;
        let has_body = !matches!(body, Body::None);
        if has_body {
            if self.fn_visibility() != self.own_module() && !open_closed {
                return self.reject_at_sig(traits::OPEN_CLOSED_REQUIRED);
            }
        } else if in_trait && open_closed {
            return self.reject_at_sig(traits::OPEN_ON_DECL);
        }
        Ok(())
    }

    /// Read the leading header statements (`requires(..)`, `ensures(..)`,
    /// `recommends(..)`) of a body; returns how many statements they were.
    ///
    /// Verus takes one call of each kind (`vir/src/headers.rs`,
    /// `read_header_block`) and rejects a second at its statement. A clause
    /// written in the signature is such a call too, ahead of the body's.
    fn header(
        &mut self,
        block: &'tcx hir::Block<'tcx>,
        requires: &mut Vec<Clause>,
        ensures: &mut Vec<Clause>,
        recommends: &mut Vec<Clause>,
    ) -> R<usize> {
        let mut count = 0;
        let mut seen: Vec<VerusItem> = Vec::new();
        // Verus builds an `external_body` function's body without its
        // `decreases`, `when` and `decreases_by` headers
        // (`fn_call_to_vir.rs`, the `bctx.external_body` test).
        let external_body = attrs::item_attrs(
            self.tcx
                .hir_attrs(self.tcx.local_def_id_to_hir_id(self.body_def)),
        )
        .external_body;
        let mut seen_termination: Vec<&'static str> = Vec::new();
        for stmt in block.stmts {
            if self.is_unwrap_parameter(stmt) {
                return refuse(
                    "unwrap-parameter",
                    "a `header_unwrap_parameter` statement, which Verus pairs with the next one",
                    stmt.span,
                );
            }
            if let hir::StmtKind::Semi(e) | hir::StmtKind::Expr(e) = stmt.kind {
                if self.is_no_method_body(e) {
                    return Err(FnProblem::Rejected(UserError::new(
                        Phase::RustToVir,
                        stmt.span,
                        messages::traits::NO_METHOD_BODY_STATEMENT,
                    )));
                }
            }
            let hir::StmtKind::Semi(e) = stmt.kind else {
                break;
            };
            let hir::ExprKind::Call(func, args) = e.kind else {
                break;
            };
            let Some((item, item_def)) = self.callee_item(func) else {
                break;
            };
            if !item.is_header() {
                break;
            }
            if matches!(item, VerusItem::NoUnwind | VerusItem::NoUnwindWhen)
                && self.unwind.is_some()
            {
                return Err(FnProblem::Rejected(UserError::new(
                    Phase::RustToVir,
                    e.span,
                    messages::header::SECOND_UNWIND,
                )));
            }
            if let Some(message) = messages::header::second_call(item) {
                if seen.contains(&item) {
                    return Err(FnProblem::Rejected(UserError::new(
                        Phase::RustToVir,
                        e.span,
                        message,
                    )));
                }
                seen.push(item);
            }
            match (item, args) {
                (VerusItem::OpensInvariantsNone, []) => {
                    self.opens_none = true;
                    count += 1;
                    continue;
                }
                (VerusItem::NoUnwind, []) => {
                    self.unwind = Some(UnwindSpec::NoUnwind);
                    count += 1;
                    continue;
                }
                _ => {}
            }
            let [arg] = args else {
                return refuse("header-shape", "a header call without one argument", e.span);
            };
            match item {
                VerusItem::NoUnwindWhen => {
                    self.area = Area::Unwind;
                    let condition = self.spec(arg)?;
                    if condition.ty != Ty::Bool {
                        return refuse(
                            "header-shape",
                            "a no_unwind_when condition that is not Boolean",
                            arg.span,
                        );
                    }
                    if let Some((name, at)) = self.mut_ref_read(&condition) {
                        self.errors.push(UserError::new(Phase::WellFormed, at,
                            format!("in opens_invariants clause, use `old({name})` to refer to the pre-state of an &mut variable")));
                    }
                    self.unwind = Some(UnwindSpec::NoUnwindWhen(condition));
                }
                VerusItem::Requires => {
                    self.area = Area::Requires;
                    requires.extend(self.clause_list(arg, item)?);
                }
                VerusItem::Recommends => {
                    self.area = Area::Recommends;
                    recommends.extend(self.clause_list(arg, item)?);
                }
                VerusItem::Ensures => {
                    self.area = Area::Ensures;
                    ensures.extend(self.ensures_clauses(arg)?);
                }
                VerusItem::Returns => self.read_returns_clause(item_def, e, arg)?,
                VerusItem::OtherHeader
                    if external_body
                        && matches!(
                            self.tcx.item_name(item_def).as_str(),
                            "decreases" | "decreases_when" | "decreases_by" | "recommends_by"
                        ) => {}
                VerusItem::OtherHeader => match self.tcx.item_name(item_def).as_str() {
                    name @ ("decreases" | "decreases_when" | "decreases_by" | "recommends_by")
                        if seen_termination.contains(&termination_slot(name)) =>
                    {
                        return Err(FnProblem::Rejected(UserError::new(
                            Phase::RustToVir,
                            stmt.span,
                            messages::termination::second_header(termination_slot(name)),
                        )));
                    }
                    "decreases" => {
                        seen_termination.push("decreases");
                        self.decreases_header(arg)?;
                    }
                    "decreases_when" => {
                        seen_termination.push("decreases_when");
                        self.area = Area::When;
                        let cond = self.spec(arg)?;
                        if cond.ty != Ty::Bool {
                            return refuse(
                                "header-shape",
                                "a decreases_when that is not a bool",
                                arg.span,
                            );
                        }
                        self.decreases_when = Some(cond);
                    }
                    "extra_dependency" => {
                        let target = match &arg.kind {
                            hir::ExprKind::Path(qpath) => {
                                match self.typeck.qpath_res(qpath, arg.hir_id) {
                                    Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => {
                                        self.cx.fns.get(&def_id).map(|info| info.id)
                                    }
                                    _ => None,
                                }
                            }
                            _ => None,
                        };
                        let Some(target) = target else {
                            return refuse(
                                "header-shape",
                                "an extra_dependency that does not name a function of this crate",
                                arg.span,
                            );
                        };
                        self.cx
                            .extra_deps
                            .borrow_mut()
                            .entry(self.own_id)
                            .or_default()
                            .push(target);
                    }
                    "decreases_by" | "recommends_by" => {
                        let hir::ExprKind::Path(qpath) = &arg.kind else {
                            return refuse(
                                "header-shape",
                                "a decreases_by that is not a path",
                                arg.span,
                            );
                        };
                        let target = match self.typeck.qpath_res(qpath, arg.hir_id) {
                            Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => def_id,
                            _ => {
                                return refuse(
                                    "header-shape",
                                    "a decreases_by that does not name a function",
                                    arg.span,
                                )
                            }
                        };
                        seen_termination.push("decreases_by");
                        self.decreases_by = Some((target, e.span));
                    }
                    _ => {
                        return refuse(
                            "header",
                            format!("`{}` is not read yet", self.tcx.def_path_str(item_def)),
                            e.span,
                        )
                    }
                },
                _ => {
                    return refuse(
                        "header",
                        format!("`{}` is not read yet", self.tcx.def_path_str(item_def)),
                        e.span,
                    )
                }
            }
            count += 1;
        }
        Ok(count)
    }

    /// A function's `decreases` header: one integer measure, or a tuple of
    /// them for a lexicographic measure (`fn_call_to_vir.rs`,
    /// `extract_tuple`).
    fn decreases_header(&mut self, arg: &'tcx hir::Expr<'tcx>) -> R<()> {
        self.area = Area::Decreases;
        let parts: Vec<&'tcx hir::Expr<'tcx>> = match arg.kind {
            hir::ExprKind::Tup(parts) => parts.iter().collect(),
            _ => vec![arg],
        };
        for part in parts {
            if let Some((attr, span)) = attrs::verus_attrs(self.tcx.hir_attrs(part.hir_id)).first()
            {
                return refuse(
                    "attribute",
                    format!("{attr:?} on a decreases clause"),
                    *span,
                );
            }
            let value = self.spec(part)?;
            if value.ty.int_range().is_none() {
                return refuse(
                    "decreases-type",
                    "a decreases measure that is not an integer",
                    part.span,
                );
            }
            // `well_formed.rs`, `check_var`: a measure reads a `&mut`
            // parameter's value at entry, through `old`.
            if let Some((name, at)) = self.mut_ref_read(&value) {
                self.errors.push(UserError::new(
                    Phase::WellFormed,
                    at,
                    messages::termination::decreases_mut_ref(&name),
                ));
            }
            let value = match value.ty.int_range() {
                Some(trust_vc_vcir::IntRange::Int) => value,
                _ => value.cast(
                    trust_vc_vcir::CastKind::Exact,
                    Ty::int(),
                    self.sp(part.span),
                ),
            };
            self.decreases.push(value);
        }
        Ok(())
    }

    /// Refuse a header call left in an `external_body` body after its
    /// leading header statements (`stmts` and `tail` are the rest of the
    /// body). Verus builds such a body from its header calls alone
    /// (`rust_to_vir_expr.rs`, `expr_to_vir_inner` and `stmt_to_vir`;
    /// `fn_call_to_vir.rs`): a `let` or item statement is dropped, so is
    /// every expression but a block, a call or a closure, and so is a call
    /// of anything but a header. A header call reached through blocks
    /// after a dropped statement is still read as the function's (and a
    /// block of them is hoisted, `read_header`), which [`Self::header`]
    /// does not follow.
    ///
    /// What Verus does convert there is checked as Verus would, or refused:
    /// see [`Self::external_body_expr`].
    fn external_body_headers(
        &self,
        stmts: &[hir::Stmt<'_>],
        tail: Option<&hir::Expr<'_>>,
    ) -> R<()> {
        if let Some(stmt) = stmts.iter().find(|stmt| self.is_unwrap_parameter(stmt)) {
            return refuse(
                "unwrap-parameter",
                "a `header_unwrap_parameter` statement, which Verus pairs with the next one",
                stmt.span,
            );
        }
        let exprs = stmts
            .iter()
            .filter_map(|stmt| match stmt.kind {
                hir::StmtKind::Semi(e) | hir::StmtKind::Expr(e) => Some(e),
                hir::StmtKind::Let(_) | hir::StmtKind::Item(_) => None,
            })
            .chain(tail);
        for e in exprs {
            self.external_body_expr(e)?;
        }
        Ok(())
    }

    /// A statement marked `#[verus::internal(header_unwrap_parameter)]`.
    /// Verus converts it together with the statement after it, into the
    /// header of a `Tracked(x)` or `Ghost(x)` parameter, or reports an
    /// ill-formed header (`rust_to_vir_expr.rs`, `stmts_to_vir`).
    fn is_unwrap_parameter(&self, stmt: &hir::Stmt<'_>) -> bool {
        attrs::verus_attrs(self.tcx.hir_attrs(stmt.hir_id))
            .iter()
            .any(|(attr, _)| {
                matches!(attr, VerusAttr::Unknown(name)
                    if name == "verus::internal(header_unwrap_parameter)")
            })
    }

    /// One expression of an `external_body` body that Verus converts
    /// (`rust_to_vir_expr.rs`, `expr_to_vir_inner`): a block, a call or a
    /// closure; anything else becomes an empty block. Verus converts a
    /// block's statements the same way, a tuple-constructor call's
    /// arguments too, and no other call's. Every converted expression has
    /// its type translated (`mid_ty_to_vir`). A closure is converted in
    /// full (`closure_to_vir`, with its own header rules), which the reader
    /// does not model: it is refused, and so is an `async` block (a
    /// closure in HIR), a labeled block, a block with another Verus
    /// attribute, a type Verus does not translate and an adjustment other
    /// than `!` to any type.
    fn external_body_expr(&self, e: &hir::Expr<'_>) -> R<()> {
        let e = e.peel_drop_temps();
        let shape = |what: &str| {
            refuse(
                "external-body-expr",
                format!("{what} in an `external_body` body, which Verus converts"),
                e.span,
            )
        };
        match e.kind {
            hir::ExprKind::Block(..) | hir::ExprKind::Call(..) => {}
            hir::ExprKind::Closure(_) => return shape("a closure or async block"),
            _ => return Ok(()),
        }
        let types = std::iter::once(self.typeck.node_type(e.hir_id))
            .chain(self.typeck.expr_adjustments(e).iter().map(|a| a.target));
        let env = self.body_def.to_def_id();
        for ty in types {
            if let Some(problem) = self
                .cx
                .verus_ty_problem(ty, env)
                .map_err(FnProblem::Refused)?
            {
                return shape(&format!(
                    "an expression whose type Verus does not translate ({problem})"
                ));
            }
        }
        if self
            .typeck
            .expr_adjustments(e)
            .iter()
            .any(|a| !matches!(a.kind, Adjust::NeverToAny))
        {
            return shape("an adjusted expression");
        }
        match e.kind {
            hir::ExprKind::Block(block, label) => {
                if label.is_some() {
                    return shape("a labeled block");
                }
                // An invariant block is converted by its own rules, and a
                // ghost wrapper on a block is Verus's error.
                let other_attr =
                    attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id))
                        .iter()
                        .any(|(attr, _)| match attr {
                            VerusAttr::Unknown(_) => true,
                            VerusAttr::OtherGhostBlock(name) => name.ends_with("ghost_wrapper"),
                            _ => false,
                        });
                if other_attr {
                    return shape("a block with a Verus attribute");
                }
                self.external_body_headers(block.stmts, block.expr)
            }
            hir::ExprKind::Call(func, args) => {
                if let Some((item, item_def)) = self.callee_item(func) {
                    if item.is_header() {
                        return refuse(
                            "header-position",
                            format!(
                                "`{}` after other statements of an `external_body` body",
                                self.tcx.def_path_str(item_def)
                            ),
                            e.span,
                        );
                    }
                }
                let hir::ExprKind::Path(qpath) = &func.kind else {
                    return Ok(());
                };
                match self.typeck.qpath_res(qpath, func.hir_id) {
                    Res::Def(DefKind::Ctor(_, CtorKind::Fn), _) | Res::SelfCtor(_) => {
                        args.iter().try_for_each(|arg| self.external_body_expr(arg))
                    }
                    Res::Def(..) | Res::Local(_) => Ok(()),
                    _ => shape("a call of this callee"),
                }
            }
            _ => Ok(()),
        }
    }

    /// The `hide` calls among `stmts` (a body's statements after its
    /// `requires`/`ensures`/`recommends`) that Verus takes as headers of the
    /// function (`vir/src/headers.rs`, `read_header`): a statement that is a
    /// `hide`, or a plain block whose statements are all `hide`s, before the
    /// first other statement. Every statement but a `use` counts as one,
    /// even an empty block or `();`. A `hide` anywhere else stays in the
    /// body, where Verus's well-formedness check rejects it.
    ///
    /// Verus lifts the `hide`s out of a plain block statement when the block
    /// holds one, and drops the block's other statements (or reports an
    /// internal error); such a block is refused.
    fn leading_hides(&self, stmts: &[hir::Stmt<'_>]) -> R<HashSet<HirId>> {
        let mut hides = HashSet::new();
        let mut leading = true;
        for stmt in stmts {
            let e = match stmt.kind {
                hir::StmtKind::Semi(e) | hir::StmtKind::Expr(e) => e,
                // `use` items make no statement; other items are refused
                // where they are read.
                hir::StmtKind::Item(_) => continue,
                hir::StmtKind::Let(_) => {
                    leading = false;
                    continue;
                }
            };
            if self.is_hide(e) {
                if leading {
                    hides.insert(e.hir_id);
                }
                continue;
            }
            if let hir::ExprKind::Block(block, None) = e.kind {
                if !self.is_ghost_block(e) {
                    let nested: Vec<HirId> = block
                        .stmts
                        .iter()
                        .filter_map(|s| match s.kind {
                            hir::StmtKind::Semi(inner) | hir::StmtKind::Expr(inner)
                                if self.is_hide(inner) =>
                            {
                                Some(inner.hir_id)
                            }
                            _ => None,
                        })
                        .collect();
                    let tail_hide = block.expr.is_some_and(|tail| self.is_hide(tail));
                    if !nested.is_empty() || tail_hide {
                        if nested.len() != block.stmts.len() || block.expr.is_some() {
                            return refuse(
                                "header-block",
                                "a block that holds `hide` and other code",
                                e.span,
                            );
                        }
                        if leading {
                            hides.extend(nested);
                        }
                        continue;
                    }
                }
            }
            leading = false;
        }
        Ok(hides)
    }

    /// Is `e` a `hide`: a reveal with fuel 0? A suffixed fuel is not one:
    /// Verus rejects it where it reads the reveal.
    fn is_hide(&self, e: &hir::Expr<'_>) -> bool {
        let hir::ExprKind::Call(func, [_, fuel]) = e.kind else {
            return false;
        };
        matches!(self.callee_item(func), Some((VerusItem::RevealHide, _)))
            && matches!(fuel.kind, hir::ExprKind::Lit(lit)
                if matches!(lit.node, AstLitKind::Int(n, LitIntType::Unsuffixed) if n.get() == 0))
    }

    /// `ensures(|ret| [constrain_type(ret, f(..)), clauses..])`, or
    /// `ensures([clauses..])` for a function returning `()`.
    fn ensures_clauses(&mut self, arg: &'tcx hir::Expr<'tcx>) -> R<Vec<Clause>> {
        match arg.kind {
            hir::ExprKind::Closure(closure) => {
                let body = self.tcx.hir_body(closure.body);
                let [param] = body.params else {
                    return refuse(
                        "header-shape",
                        "an ensures closure without one parameter",
                        arg.span,
                    );
                };
                let PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, ident, None) =
                    param.pat.kind
                else {
                    return refuse(
                        "header-shape",
                        "a return value that is not a plain name",
                        param.pat.span,
                    );
                };
                self.local_ids.insert(pat_hir, self.ret);
                self.locals[self.ret.index()].name = ident.name.to_string();
                self.ensures_ret_ty = Some(self.pat_rty(param.pat));
                self.clause_list(body.value, VerusItem::Ensures)
            }
            _ => self.clause_list(arg, VerusItem::Ensures),
        }
    }

    /// The actual clauses of a scalar or array header argument, before
    /// clause-count checks. Only ensures filters authenticated typing aids,
    /// at every position, as extract_ensures does in the pinned reader.
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
                        if matches!(self.callee_item(func), Some((VerusItem::ConstrainType, _))) {
                            return false;
                        }
                    }
                }
                true
            })
            .collect()
    }

    /// Read every actual header clause with its own attributes and span.
    fn clause_list(&mut self, arr: &'tcx hir::Expr<'tcx>, header: VerusItem) -> R<Vec<Clause>> {
        let mut clauses = Vec::new();
        for elem in self.clause_elements(arr, header) {
            self.attr_hook(elem, false)?;
            let attrs = self.clause_attrs(elem.hir_id)?;
            let expr = self.spec(elem)?;
            if expr.ty != Ty::Bool {
                return refuse("header-shape", "a clause that is not a bool", elem.span);
            }
            clauses.push(Clause {
                expr,
                span: self.sp(elem.span),
                attrs,
            });
        }
        Ok(clauses)
    }

    fn read_native_constant(&mut self) -> R<FnDecl> {
        let span = self.tcx.def_span(self.def_id);
        if self.cx.constants.mode(self.def_id) != Some(ConstMode::Dual) {
            return refuse(
                "constant",
                "an unregistered native constant initializer",
                span,
            );
        }
        let attributes = self.cx.declaration_attrs(self.def_id);
        native_constant_attributes(self.tcx, self.def_id)?;
        if attributes.inline
            || attributes.closed
            || attributes.open
            || attributes.opaque
            || attributes.uninterp
            || attributes.ret_mode.is_some()
        {
            return refuse(
                "constant",
                "unsupported attributes on a native associated constant",
                span,
            );
        }
        let (environment, result_ty) = match self.subst {
            Some(args) => (
                ty::TypingEnv::fully_monomorphized(),
                self.tcx.type_of(self.def_id).instantiate(self.tcx, args),
            ),
            None => (
                ty::TypingEnv::non_body_analysis(self.tcx, self.def_id.to_def_id()),
                self.tcx.type_of(self.def_id).instantiate_identity(),
            ),
        };
        let native = self
            .tcx
            .try_normalize_erasing_regions(environment, result_ty)
            .map_err(|error| {
                FnProblem::Refused(Refusal::new(
                    "type",
                    format!("a constant result that could not be normalized: {error:?}"),
                    span,
                ))
            })?;
        let result = self.vc_ty(native)?.ok_or_else(|| {
            FnProblem::Refused(Refusal::new(
                "type",
                format!("a constant with unsupported result `{native}`"),
                span,
            ))
        })?;
        self.ret = self.add_local(
            self.local_decl("result", result, Mode::Exec, false, LocalKind::Return, span),
            false,
        );
        let body = self.tcx.hir_body_owned_by(self.body_def);
        self.reading_initializer = true;
        let mut effects = Vec::new();
        let value = if attributes.external_body {
            self.unit(span)
        } else {
            self.expr(body.value, Ctx::Exec, &mut effects)?
        };
        self.reading_initializer = false;
        if !effects.is_empty() {
            return refuse(
                "constant-initializer",
                "a constant initializer with unrepresented effects",
                body.value.span,
            );
        }
        if let Some(finding) = &self.attr_finding {
            return Err(attr_problem(&finding.problem));
        }
        if let Some(problem) = self.pending.take() {
            return Err(FnProblem::Refused(problem));
        }
        let copy_premises = self.native_copy_premises()?;
        Ok(FnDecl {
            id: self.own_id,
            name: self.cx.friendly_fn_path(self.def_id.to_def_id()),
            span: self.sp(span),
            mode: Mode::Spec,
            role: self.role,
            kind: FnKind::Constant(ConstMode::Dual),
            type_params: std::mem::take(&mut self.type_params),
            copy_premises,
            locals: std::mem::take(&mut self.locals),
            params: Vec::new(),
            ret: self.ret,
            requires: Vec::new(),
            ensures: Vec::new(),
            recommends: Vec::new(),
            unwind: None,
            decreases: Vec::new(),
            decreases_when: None,
            decreases_by: None,
            attrs: FnAttrs {
                external_body: attributes.external_body,
                rlimit: attributes.rlimit,
                is_trait_method_impl: self
                    .tcx
                    .trait_impl_of_assoc(self.def_id.to_def_id())
                    .is_some(),
                ..FnAttrs::default()
            },
            body: if attributes.external_body {
                Body::None
            } else {
                Body::Constant(value)
            },
        })
    }

    /// Immutable native initializer expressions retain the same actual let
    /// declarations and operation sites. No assignments, dropped statements,
    /// calls or partial bodies are converted to mathematical definitions.
    fn initializer_block(
        &mut self,
        statements: &'tcx [hir::Stmt<'tcx>],
        tail: Option<&'tcx hir::Expr<'tcx>>,
        span: Span,
    ) -> R<Expr> {
        let saved = self.reading_initializer;
        self.reading_initializer = true;
        let lowered = (|| {
            let mut bindings = Vec::new();
            for statement in statements {
                let hir::StmtKind::Let(local) = statement.kind else {
                    return refuse(
                        "constant-initializer",
                        "a non-let statement in a constant initializer",
                        statement.span,
                    );
                };
                let mut lowered = Vec::new();
                self.let_stmt(local, Ctx::Exec, &mut lowered)?;
                for statement in lowered {
                    let StmtKind::Let {
                        local,
                        init: Some(value),
                    } = statement.kind
                    else {
                        return refuse(
                            "constant-initializer",
                            "an unrepresented initializer statement",
                            span,
                        );
                    };
                    let declaration = &mut self.locals[local.index()];
                    if declaration.mutable || declaration.mode != Mode::Exec {
                        return refuse(
                            "constant-initializer",
                            "a mutable or ghost binding in an initializer",
                            span,
                        );
                    }
                    declaration.kind = LocalKind::Bound;
                    bindings.push((local, value, statement.span));
                }
            }
            let mut effects = Vec::new();
            let mut value = match tail {
                Some(tail) => self.expr(tail, Ctx::Exec, &mut effects)?,
                None => self.unit(span),
            };
            if !effects.is_empty() {
                return refuse(
                    "constant-initializer",
                    "a constant value with unrepresented effects",
                    span,
                );
            }
            for (local, initial, at) in bindings.into_iter().rev() {
                value = Expr::new(
                    value.ty.clone(),
                    at,
                    ExprKind::Let {
                        local,
                        value: Box::new(initial),
                        body: Box::new(value),
                    },
                );
            }
            Ok(value)
        })();
        self.reading_initializer = saved;
        lowered
    }

    /// The body of a spec function. Normally a pure expression; if it
    /// assigns, it is lowered as statements so that the VcIR checker reports
    /// Verus's "assignment is not allowed inside pure context".
    fn spec_fn_body(
        &mut self,
        rest: &'tcx [hir::Stmt<'tcx>],
        tail: Option<&'tcx hir::Expr<'tcx>>,
        span: Span,
    ) -> R<Body> {
        let assigns = rest.iter().any(|s| match s.kind {
            hir::StmtKind::Semi(e) | hir::StmtKind::Expr(e) => {
                matches!(
                    e.kind,
                    hir::ExprKind::Assign(..) | hir::ExprKind::AssignOp(..)
                )
            }
            _ => false,
        });
        if assigns {
            let mut out = Vec::new();
            for stmt in rest {
                self.stmt(stmt, Ctx::Spec, &mut out)?;
            }
            if let Some(tail) = tail {
                self.stmt_expr(tail, Ctx::Spec, &mut out)?;
            }
            return Ok(Body::Stmts(Block::new(out)));
        }
        if tail.is_none() {
            // A block without a value is a statement to Verus, which it
            // rejects when it turns the body into a pure expression
            // (`ast_to_sst.rs`), just before verifying the module.
            self.errors
                .push(UserError::new(Phase::Sst, span, messages::EXPECTED_PURE));
        }
        Ok(Body::Spec(self.spec_block(rest, tail, span, true)?))
    }

    /// The statements of an exec or proof body, ending in a `Return` that
    /// carries the value of the tail expression.
    fn stmt_body(
        &mut self,
        rest: &'tcx [hir::Stmt<'tcx>],
        block: &'tcx hir::Block<'tcx>,
        ctx: Ctx,
        ret_ty: &Ty,
    ) -> R<Block> {
        let mut out = Vec::new();
        for stmt in rest {
            self.stmt(stmt, ctx, &mut out)?;
        }
        match block.expr {
            Some(tail) if matches!(tail.kind, hir::ExprKind::Ret(_)) => {
                self.stmt_expr(tail, ctx, &mut out)?;
            }
            Some(tail) => {
                let value = self.expr(tail, ctx, &mut out)?;
                self.push_return(Some(value), tail.span, &mut out);
            }
            // Without a tail expression Verus points "at the end of the
            // function body" at the function's signature.
            None if *ret_ty == Ty::Unit => {
                let hir_id = self.tcx.local_def_id_to_hir_id(self.def_id);
                let span = self
                    .tcx
                    .hir_node(hir_id)
                    .fn_sig()
                    .map_or(block.span, |sig| sig.span);
                self.push_return(None, span, &mut out);
            }
            // A non-unit body without a tail diverges (it ends in `return`
            // or a panic); there is no fall-through exit.
            None => {}
        }
        Ok(Block::new(out))
    }

    /// Push a `Return` at `span`; returns the span's id.
    fn push_return(&mut self, value: Option<Expr>, span: Span, out: &mut Vec<Stmt>) -> SpanId {
        let site = self.site();
        let id = self.sp(span);
        out.push(Stmt::new(id, StmtKind::Return { value, site }));
        id
    }

    // ------------------------------------------------------------------
    // Statements
    // ------------------------------------------------------------------

    fn stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>, ctx: Ctx, out: &mut Vec<Stmt>) -> R<()> {
        match stmt.kind {
            hir::StmtKind::Let(local) => self.let_stmt(local, ctx, out),
            hir::StmtKind::Item(_) => {
                refuse("stmt-item", "an item inside a function body", stmt.span)
            }
            hir::StmtKind::Expr(e) | hir::StmtKind::Semi(e) => self.stmt_expr(e, ctx, out),
        }
    }

    fn let_stmt(
        &mut self,
        local: &'tcx hir::LetStmt<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        if matches!(local.source, LocalSource::AssignDesugar) {
            // Verus points at the assigned pattern, `(a, b)` in `(a, b) = ..`.
            return Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                local.pat.span,
                messages::unsupported("destructuring assignment"),
            )));
        }
        if local.els.is_some() {
            return refuse("let-else", "`let .. else`", local.span);
        }
        // A tracked local needs a checked declaration in a body whose
        // original MIR retains its ownership uses. Prophecy markers use the
        // original declared mode, before the ghost-block promotion.
        let native_mode = match local.pat.kind {
            PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) => self
                .cx
                .native_ownership
                .borrow()
                .get(&self.def_id)
                .and_then(|ownership| ownership.local_mode(local.hir_id, binding)),
            _ => None,
        };
        let mut declared_mode = None;
        let local_attrs = self.tcx.hir_attrs(local.hir_id);
        for (attr, span) in attrs::verus_attrs(local_attrs) {
            if let VerusAttr::Mode(mode) = &attr {
                declared_mode.get_or_insert(*mode);
            }
            match attr {
                VerusAttr::Mode(mode) if native_mode == Some(mode) => {}
                VerusAttr::Mode(Mode::Spec) => {}
                VerusAttr::Prophetic | VerusAttr::LetMarker(_) => {}
                // A function the mode checker rejected is only read for
                // errors of earlier phases, which a `let`'s mode does not
                // change.
                VerusAttr::Mode(_) | VerusAttr::InferMode if self.mode_rejected => {}
                VerusAttr::InferMode => {
                    self.checked_inferred_value_mode(local)?;
                }
                _ => return refuse("attribute", format!("{attr:?} on a let"), span),
            }
        }
        let original_mode = declared_mode.unwrap_or(if self.mode == Mode::Proof {
            Mode::Spec
        } else {
            self.mode
        });
        let prophecy = attrs::local_prophecy(local_attrs, original_mode);
        let ctx = if declared_mode == Some(Mode::Spec)
            && ctx == Ctx::Exec
            && !self.cx.legacy_functions.contains(&self.def_id)
        {
            Ctx::Proof
        } else {
            ctx
        };
        let local_mode = native_mode.unwrap_or(ctx.local_mode());
        match local.pat.kind {
            PatKind::Binding(BindingMode(ByRef::No, mutability), pat_hir, ident, None)
                if matches!(self.pat_rty(local.pat).kind(), ty::Closure(..)) =>
            {
                // A closure bound to a name. Closures are not read, so the
                // function is refused unless a Verus error rejects it first;
                // reading continues so that, for example, Verus's spec `==`
                // type error on the closure is still found. The local gets a
                // placeholder type and no initializer; the lowered function
                // is never used because the refusal stands.
                let span = local.init.map_or(local.span, |init| init.span);
                if self.pending.is_none() {
                    self.pending = Some(Refusal::new("closure", "closures are not read yet", span));
                }
                let id = self.add_local(
                    self.local_decl(
                        ident.name.as_str(),
                        Ty::Unit,
                        local_mode,
                        mutability.is_mut(),
                        LocalKind::Let,
                        local.pat.span,
                    ),
                    local.init.is_some(),
                );
                self.locals[id.index()].prophecy = prophecy;
                self.local_ids.insert(pat_hir, id);
                Ok(())
            }
            PatKind::Binding(BindingMode(ByRef::No, mutability), pat_hir, ident, None) => {
                // The initializer first: it runs first, and a refusal names
                // what it contains (a closure, say) rather than its type.
                let init = match local.init {
                    Some(init) => Some(self.expr(init, ctx, out)?),
                    None => None,
                };
                let rustc_ty = self.pat_rty(local.pat);
                let Some(ty) = self.vc_ty(rustc_ty)? else {
                    return refuse(
                        "type",
                        format!("`{ident}` has type `{rustc_ty}`"),
                        local.pat.span,
                    );
                };
                let local_mode = self.checked_binding_mode(local.pat, ctx)?;
                let id = self.add_local(
                    self.local_decl(
                        ident.name.as_str(),
                        ty,
                        local_mode,
                        mutability.is_mut(),
                        LocalKind::Let,
                        local.pat.span,
                    ),
                    init.is_some(),
                );
                self.locals[id.index()].prophecy = prophecy;
                self.local_ids.insert(pat_hir, id);
                let statement = match (local.init, init) {
                    (Some(source), Some(value)) => {
                        self.legacy_value_declaration(id, value, source, ctx, Some(local_mode))?
                    }
                    (_, init) => StmtKind::Let { local: id, init },
                };
                out.push(Stmt::new(self.sp(local.span), statement));
                Ok(())
            }
            PatKind::Tuple(..) | PatKind::Struct(..) | PatKind::TupleStruct(..) => {
                if Self::has_struct_pattern(local.pat) {
                    if let Some(init) = local.init {
                        self.local_struct_source(init, "let-pattern")?;
                    }
                }
                // Evaluate the initializer once, before introducing any of
                // the pattern's names. Every binding reads a projection of
                // this saved value, including nested patterns and `..`.
                let value = match local.init {
                    Some(source) => {
                        let init = self.expr(source, ctx, out)?;
                        let mode = self.legacy_saved_value_mode(source, &init, ctx)?;
                        let saved = self.temp_with_mode(init.ty.clone(), mode, local.span);
                        if mode == Mode::Spec && ctx == Ctx::Exec {
                            self.locals[saved.index()].prophecy = DeclProphecy::DelayedInfer;
                        }
                        let declaration =
                            self.legacy_value_declaration(saved, init, source, ctx, None)?;
                        out.push(Stmt::new(self.sp(local.span), declaration));
                        Some(self.read_local(saved, local.span))
                    }
                    None => None,
                };
                self.value_let_bindings(local.pat, value, ctx, LocalKind::Let, out)?;
                self.pattern_prophecy(local.pat, prophecy);
                Ok(())
            }
            PatKind::Wild => match local.init {
                Some(init) => self.stmt_expr(init, ctx, out),
                None => Ok(()),
            },
            _ => refuse(
                "let-pattern",
                "a `let` pattern that is not a plain name",
                local.pat.span,
            ),
        }
    }

    /// An expression in statement position: its value is discarded.
    fn stmt_expr(&mut self, e: &'tcx hir::Expr<'tcx>, ctx: Ctx, out: &mut Vec<Stmt>) -> R<()> {
        self.attr_hook(e, false)?;
        self.stmt_expr_unhooked(e, ctx, out)?;
        // A `DropTemps` is read through: its inner expression carries the
        // coercion Verus sees.
        if !matches!(e.kind, hir::ExprKind::DropTemps(_)) && self.never_to_any(e) {
            self.push_unreachable(e.span, out);
        }
        self.attr_hook(e, true)
    }

    /// Does rustc coerce `e` from `!` to another type? Verus reads that
    /// coercion as `NeverToAny`, which ends the block `e` is in
    /// (`ast_to_sst.rs`); a `!` expression without it, such as the
    /// statement `break;`, does not.
    fn never_to_any(&self, e: &hir::Expr<'_>) -> bool {
        self.typeck
            .expr_adjustments(e)
            .iter()
            .any(|a| matches!(a.kind, Adjust::NeverToAny))
    }

    /// Mark the end of a coerced `!` expression, once.
    fn push_unreachable(&self, span: Span, out: &mut Vec<Stmt>) {
        if !matches!(out.last().map(|s| &s.kind), Some(StmtKind::Unreachable)) {
            out.push(Stmt::new(self.sp(span), StmtKind::Unreachable));
        }
    }

    fn stmt_expr_unhooked(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        // A loop reads its own attributes.
        if let hir::ExprKind::Loop(block, label, source, header) = e.kind {
            return self.loop_stmt(e, block, label, source, header, ctx, out);
        }
        let mut proof_block = false;
        if super::modes::is_proof_in_spec(self.tcx, e) {
            // A `proof { .. }` block of spec code, in code that is not a
            // spec function's body.
            self.proof_in_spec_expr(e)?;
            return Ok(());
        }
        for (attr, span) in attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id)) {
            match attr {
                VerusAttr::ProofBlock => proof_block = true,
                VerusAttr::OtherGhostBlock(name) => {
                    return refuse(
                        "ghost-block",
                        format!("a `{name}` block is not read yet"),
                        span,
                    )
                }
                other => return refuse("attribute", format!("{other:?} on a statement"), span),
            }
        }
        if proof_block {
            return self.proof_block(e, ctx, out);
        }
        match e.kind {
            hir::ExprKind::DropTemps(inner) => self.stmt_expr(inner, ctx, out),
            hir::ExprKind::Assign(lhs, rhs, _) => self.assign(e, lhs, rhs, ctx, out),
            hir::ExprKind::AssignOp(op, lhs, rhs) => {
                let bin = assign_op_kind(op.node);
                self.assign_op(e, bin, lhs, rhs, ctx, out)
            }
            hir::ExprKind::Ret(value) => {
                // A proof function may return; a proof block inside exec
                // code may not leave the exec function.
                if ctx.ghost() && self.mode != Mode::Proof && !self.mode_rejected {
                    return refuse("expr", "`return` inside ghost code", e.span);
                }
                let value = match value {
                    Some(v) => Some(self.expr(v, ctx, out)?),
                    None => None,
                };
                let span = self.push_return(value, e.span, out);
                self.cx.mark_explicit_return(span);
                Ok(())
            }
            hir::ExprKind::Block(block, None) => {
                let mut inner = Vec::new();
                self.block_stmts(block, ctx, &mut inner)?;
                out.push(Stmt::new(
                    self.sp(e.span),
                    StmtKind::Block(Block::new(inner)),
                ));
                Ok(())
            }
            hir::ExprKind::Call(func, args) => {
                let value = self.call(e, func, args, ctx, out, true)?;
                self.keep_discarded(value, ctx, e.span, out);
                Ok(())
            }
            hir::ExprKind::Break(dest, None) => self.break_continue(e, &dest, true, ctx, out),
            hir::ExprKind::Break(_, Some(_)) => {
                refuse("break-value", "a break with a value", e.span)
            }
            hir::ExprKind::Continue(dest) => self.break_continue(e, &dest, false, ctx, out),
            _ => {
                let value = self.expr(e, ctx, out)?;
                self.keep_discarded(value, ctx, e.span, out);
                Ok(())
            }
        }
    }

    /// Keep a discarded value that has check sites (its overflow checks
    /// still apply) in a temporary. The calls of a value dropped otherwise
    /// are still edges of Verus's call graph.
    fn keep_discarded(&mut self, value: Expr, ctx: Ctx, span: Span, out: &mut Vec<Stmt>) {
        if !has_checks(&value) {
            let mut callees = Vec::new();
            walk_expr(&value, &mut |e| {
                if let ExprKind::Call { callee, .. } = &e.kind {
                    callees.push(*callee);
                }
            });
            if !callees.is_empty() {
                self.cx
                    .dropped_calls
                    .borrow_mut()
                    .entry(self.own_id)
                    .or_default()
                    .extend(callees);
            }
            return;
        }
        let t = self.temp(value.ty.clone(), ctx, span);
        out.push(Stmt::new(
            self.sp(span),
            StmtKind::Let {
                local: t,
                init: Some(value),
            },
        ));
    }

    /// Whether `e` carries one of Verus's ghost-block attributes. A ghost
    /// block is ghost code wherever it appears, as a statement or for its
    /// value (the tail of a block or an `if` branch, a `let` initializer,
    /// an argument), so both positions read it through [`Self::stmt_expr`].
    fn is_ghost_block(&self, e: &hir::Expr<'_>) -> bool {
        attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id))
            .iter()
            .any(|(attr, _)| matches!(attr, VerusAttr::ProofBlock | VerusAttr::OtherGhostBlock(_)))
    }

    /// A `proof { .. }` block in exec code: its statements are proof code,
    /// erased at run time. Verus's mode checker (`modes.rs`, `ExprX::Ghost`)
    /// requires the block to have type `()` before it reads the block.
    fn proof_block(&mut self, e: &'tcx hir::Expr<'tcx>, ctx: Ctx, out: &mut Vec<Stmt>) -> R<()> {
        let hir::ExprKind::Block(block, None) = e.kind else {
            return refuse(
                "expr",
                "`proof_block` on something that is not a block",
                e.span,
            );
        };
        if ctx != Ctx::Exec && !self.mode_rejected {
            return refuse("expr", "a proof block inside ghost code", e.span);
        }
        if !self.expr_rty(e).is_unit() {
            self.errors.push(UserError::new(
                Phase::Modes,
                e.span,
                messages::PROOF_BLOCK_NOT_UNIT,
            ));
        }
        let mut ghost = Vec::new();
        let original_tail = if self.mode_rejected { None } else { block.expr };
        let Some(original_tail) = original_tail else {
            self.block_stmts(block, Ctx::Proof, &mut ghost)?;
            out.push(Stmt::new(
                self.sp(e.span),
                StmtKind::Ghost(Block::new(ghost)),
            ));
            return Ok(());
        };
        for statement in block.stmts {
            self.stmt(statement, Ctx::Proof, &mut ghost)?;
        }
        let tail = self.expr(original_tail, Ctx::Proof, &mut ghost)?;
        let span = self.sp(e.span);
        let checked = self.checked_modes.as_ref().ok_or_else(|| {
            FnProblem::Refused(Refusal::new(
                "ghost-tail-modes",
                "a native ghost tail lacks a completed mode walk",
                e.span,
            ))
        })?;
        let occurrence = checked
            .ghost_tails
            .expected(
                self.tcx,
                self.def_id,
                self.body_def,
                e,
                original_tail,
                (self.own_id, span),
            )
            .map_err(|message| {
                FnProblem::Refused(Refusal::new("ghost-tail-modes", message, e.span))
            })?;
        self.ghost_tail_occurrences.push(occurrence);
        out.push(Stmt::new(
            span,
            StmtKind::GhostTail {
                block: Block::new(ghost),
                tail,
            },
        ));
        Ok(())
    }

    /// A ghost block used for its value, read as a statement. A proof
    /// block's value is `()`. A proof block of another type is a Verus error
    /// ([`Self::proof_block`]) that rejects the crate before anything is
    /// verified; an uninitialized temporary of the type the value is used at
    /// stands in for it.
    fn ghost_block_value(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        self.stmt_expr(e, ctx, out)?;
        let span = e.span;
        let adjusted = self.expr_rty_adj(e);
        if adjusted.is_unit() {
            return Ok(self.unit(span));
        }
        let Some(ty) = self.vc_ty(adjusted)? else {
            return refuse("type", format!("a proof block used as `{adjusted}`"), span);
        };
        let t = self.temp(ty, ctx, span);
        out.push(Stmt::new(
            self.sp(span),
            StmtKind::Let {
                local: t,
                init: None,
            },
        ));
        Ok(self.read_local(t, span))
    }

    /// The statements of a block and its tail, as statements.
    fn block_stmts(
        &mut self,
        block: &'tcx hir::Block<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        for stmt in block.stmts {
            self.stmt(stmt, ctx, out)?;
        }
        if let Some(tail) = block.expr {
            self.stmt_expr(tail, ctx, out)?;
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Loops
    // ------------------------------------------------------------------

    /// A `while` or `loop` (`rust_to_vir_expr.rs`, `ExprKind::Loop`). rustc
    /// lowers `while c { b }` to `loop { if c { b } else { break } }`; the
    /// loop's specification is the header statements `verus!` puts at the
    /// start of `b` (`builtin_macros`, `add_loop_specs`).
    #[allow(clippy::too_many_arguments)]
    fn loop_stmt(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        block: &'tcx hir::Block<'tcx>,
        label: Option<rustc_ast::Label>,
        source: hir::LoopSource,
        header: Span,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        // Verus's mode checker rejects a loop in ghost code; the mode
        // checker here reports it.
        if ctx != Ctx::Exec && !self.mode_rejected {
            return refuse("loop-in-ghost", "a loop in ghost code", header);
        }
        let mut isolation_attr = None;
        let mut complex_attr = false;
        for (attr, span) in attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id)) {
            match attr {
                VerusAttr::LoopIsolation(flag) => isolation_attr = Some(flag),
                VerusAttr::AllowComplexInvariants => complex_attr = true,
                VerusAttr::Unknown(name) if name == "verus::internal(for_loop)" => {
                    return refuse("for-loop", "for loops are not read yet", span)
                }
                other => return refuse("attribute", format!("{other:?} on a loop"), span),
            }
        }
        let isolation = isolation_attr
            .or(self.loop_settings.isolation)
            .unwrap_or(true);
        let allow_complex = complex_attr || self.loop_settings.allow_complex_invariants;
        let (cond, body) = match source {
            hir::LoopSource::While => {
                let (
                    [],
                    Some(hir::Expr {
                        kind: hir::ExprKind::If(cond, then_expr, Some(else_expr)),
                        ..
                    }),
                ) = (block.stmts, block.expr)
                else {
                    return refuse("loop-shape", "a while loop of an unexpected shape", header);
                };
                let hir::ExprKind::Block(body, None) = then_expr.kind else {
                    return refuse("loop-shape", "a while loop of an unexpected shape", header);
                };
                if !is_plain_break_block(else_expr) {
                    return refuse("loop-shape", "a while loop of an unexpected shape", header);
                }
                (Some(*cond), body)
            }
            hir::LoopSource::Loop => (None, block),
            hir::LoopSource::ForLoop => {
                return refuse("for-loop", "for loops are not read yet", header)
            }
        };
        let label = label.map(|l| l.ident.name);
        if label.is_some() && self.loops.iter().any(|scope| scope.label == label) {
            // Verus matches `break` to loops by label name.
            return refuse("loop-label", "a loop label that shadows another", header);
        }

        // The condition, evaluated before every iteration.
        let cond = match cond {
            Some(cond) => {
                let mut cond_out = Vec::new();
                let value = self.expr(cond, ctx, &mut cond_out)?;
                if value.ty != Ty::Bool {
                    return refuse(
                        "loop-shape",
                        "a while condition that is not a bool",
                        cond.span,
                    );
                }
                Some(LoopCond {
                    block: Block::new(cond_out),
                    expr: value,
                })
            }
            None => None,
        };
        let spec = self.loop_header(body)?;

        // `ast_to_sst.rs` rejects these before it reads the body.
        let simple = spec
            .invariants
            .iter()
            .all(|inv| inv.kind == InvariantKind::Always);
        let mut well_formed = (isolation, allow_complex);
        if allow_complex && isolation {
            self.errors.push(UserError::new(
                Phase::Sst,
                header,
                messages::loops::COMPLEX_WITH_ISOLATION,
            ));
            well_formed = (true, false);
        } else if !isolation && !simple && !allow_complex {
            self.errors.push(UserError::new(
                Phase::Sst,
                header,
                messages::loops::COMPLEX_WITHOUT_ALLOW,
            ));
            well_formed = (true, false);
        }
        // `assume_termination` on the function allows it too
        // (`ast_to_sst.rs`, `ExprX::Loop`).
        let assume_termination = attrs::item_attrs(
            self.tcx
                .hir_attrs(self.tcx.local_def_id_to_hir_id(self.def_id)),
        )
        .assume_termination;
        if spec.decreases.is_empty()
            && !self.loop_settings.allow_no_decreases
            && !assume_termination
        {
            let mut error = UserError::new(Phase::Sst, header, messages::loops::NO_DECREASES);
            error.help = Some(messages::loops::NO_DECREASES_HELP.to_string());
            self.errors.push(error);
        }

        let id = LoopId(self.next_loop);
        self.next_loop += 1;
        self.loops.push(LoopScope {
            hir_id: e.hir_id,
            id,
            label,
            isolation,
            has_decreases: !spec.decreases.is_empty(),
        });
        let mut body_out = Vec::new();
        let result = self.loop_body(body, spec.len, ctx, &mut body_out);
        self.loops.pop();
        result?;
        let sites = LoopSites {
            entry: self.site(),
            end: self.site(),
            exit: self.site(),
        };
        out.push(Stmt::new(
            self.sp(header),
            StmtKind::Loop(Box::new(Loop {
                id,
                isolation: well_formed.0,
                allow_complex_invariants: well_formed.1,
                cond,
                invariants: spec.invariants,
                decreases: spec.decreases,
                body: Block::new(body_out),
                sites,
            })),
        ));
        Ok(())
    }

    /// The statements of a loop body after its `header_len` header
    /// statements.
    fn loop_body(
        &mut self,
        body: &'tcx hir::Block<'tcx>,
        header_len: usize,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        for stmt in &body.stmts[header_len..] {
            self.stmt(stmt, ctx, out)?;
        }
        if let Some(tail) = body.expr {
            self.stmt_expr(tail, ctx, out)?;
        }
        Ok(())
    }

    /// The leading `invariant_except_break`, `invariant`, `ensures` and
    /// `decreases` statements of a loop body (`vir/src/headers.rs`,
    /// `read_header` with `HeaderAllows::Loop`).
    fn loop_header(&mut self, body: &'tcx hir::Block<'tcx>) -> R<LoopHeader> {
        let mut except_break: Option<Vec<LoopInvariant>> = None;
        let mut always: Option<Vec<LoopInvariant>> = None;
        let mut ensures: Option<Vec<LoopInvariant>> = None;
        let mut decreases: Option<Vec<Expr>> = None;
        let mut len = 0;
        for stmt in body.stmts {
            let hir::StmtKind::Semi(e) = stmt.kind else {
                break;
            };
            let hir::ExprKind::Call(func, args) = e.kind else {
                break;
            };
            let Some((item, def_id)) = self.callee_item(func) else {
                break;
            };
            if !item.is_header() {
                break;
            }
            let [arg] = args else {
                return refuse("header-shape", "a header call without one argument", e.span);
            };
            let name = self.tcx.item_name(def_id);
            let (slot, kind) = match (item, name.as_str()) {
                (VerusItem::Ensures, _) => (&mut ensures, InvariantKind::Ensures),
                (VerusItem::OtherHeader, "invariant") => (&mut always, InvariantKind::Always),
                (VerusItem::OtherHeader, "invariant_except_break") => {
                    (&mut except_break, InvariantKind::ExceptBreak)
                }
                (VerusItem::OtherHeader, "decreases") => {
                    if decreases.is_some() {
                        return refuse("loop-header", "a second decreases on a loop", e.span);
                    }
                    let parts: Vec<&'tcx hir::Expr<'tcx>> = match arg.kind {
                        hir::ExprKind::Tup(parts) => parts.iter().collect(),
                        _ => vec![arg],
                    };
                    let mut measure = Vec::new();
                    for part in parts {
                        if let Some((attr, span)) =
                            attrs::verus_attrs(self.tcx.hir_attrs(part.hir_id)).first()
                        {
                            return refuse(
                                "attribute",
                                format!("{attr:?} on a decreases clause"),
                                *span,
                            );
                        }
                        let value = self.spec(part)?;
                        if value.ty.int_range().is_none() {
                            return refuse(
                                "decreases-type",
                                "a decreases measure that is not an integer",
                                part.span,
                            );
                        }
                        measure.push(value);
                    }
                    decreases = Some(measure);
                    len += 1;
                    continue;
                }
                _ => {
                    return refuse(
                        "loop-header",
                        format!("`{}` on a loop", self.tcx.def_path_str(def_id)),
                        e.span,
                    )
                }
            };
            if slot.is_some() {
                return refuse(
                    "loop-header",
                    "a second clause list of one kind on a loop",
                    e.span,
                );
            }
            if matches!(arg.kind, hir::ExprKind::Closure(_)) {
                return refuse("loop-header", "a loop ensures that names a value", arg.span);
            }
            let mut clauses = Vec::new();
            for clause in self.clause_list(arg, item)? {
                if clause.attrs != ClauseAttrs::default() {
                    return refuse(
                        "loop-invariant-note",
                        "a proof note or custom error on a loop invariant",
                        e.span,
                    );
                }
                clauses.push(LoopInvariant {
                    kind,
                    expr: clause.expr,
                    span: clause.span,
                });
            }
            *slot = Some(clauses);
            len += 1;
        }
        let mut invariants = except_break.unwrap_or_default();
        invariants.extend(always.unwrap_or_default());
        invariants.extend(ensures.unwrap_or_default());
        Ok(LoopHeader {
            invariants,
            decreases: decreases.unwrap_or_default(),
            len,
        })
    }

    /// `break` or `continue` of an enclosing loop.
    fn break_continue(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        dest: &hir::Destination,
        is_break: bool,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        if ctx != Ctx::Exec && !self.mode_rejected {
            return refuse("ghost-break", "break or continue in ghost code", e.span);
        }
        let target = dest.target_id.ok();
        let Some(index) = self
            .loops
            .iter()
            .rposition(|scope| Some(scope.hir_id) == target)
        else {
            return refuse(
                "loop-label",
                "a break or continue of something that is not an enclosing loop",
                e.span,
            );
        };
        if !is_break && self.loops[index].has_decreases {
            // `sst_to_air.rs`, `BreakOrContinue`: from the innermost loop
            // out, up to the first whose label is the continue's, an isolated
            // loop is Verus's error.
            let label = dest.label.map(|l| l.ident.name);
            for scope in self.loops.iter().rev() {
                if scope.label == label {
                    break;
                }
                if scope.isolation {
                    return refuse(
                        "loop-continue-label",
                        "a continue Verus checks the decreases of only without isolation",
                        e.span,
                    );
                }
            }
        }
        let target = self.loops[index].id;
        let site = self.site();
        let kind = if is_break {
            StmtKind::Break { target, site }
        } else {
            StmtKind::Continue { target, site }
        };
        out.push(Stmt::new(self.sp(e.span), kind));
        Ok(())
    }

    /// Check that assigning the root of `place` is allowed.
    fn check_assign_target(&mut self, place: &Place, span: Span, ctx: Ctx) -> R<()> {
        if place.has_deref() {
            return Ok(());
        }
        let index = place.local.index();
        let decl = &self.locals[index];
        if decl.mutable || !self.initialized[index] {
            return Ok(());
        }
        match ctx {
            // rustc's borrow checker reports this (E0384) in the erase run;
            // Verus skips verification when its lifetime check finds it.
            Ctx::Exec => {
                self.deferred.get_or_insert(span);
                Ok(())
            }
            // Parameters are checked by the VcIR checker (proof functions)
            // or rejected by it for assigning at all (spec functions).
            Ctx::Proof | Ctx::Spec if decl.kind == LocalKind::Param => Ok(()),
            Ctx::Proof | Ctx::Spec => {
                self.errors.push(UserError::new(
                    Phase::Simplify,
                    span,
                    msg_not_mutable(&decl.name),
                ));
                Ok(())
            }
        }
    }

    fn assign(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        let place = self.place(lhs)?;
        self.check_assign_target(&place, e.span, ctx)?;
        let value = self.expr(rhs, ctx, out)?;
        let assignment = if self.legacy_spec_assignment(e, lhs, rhs, &place, &value, ctx)? {
            StmtKind::AssignSpec { place, value }
        } else {
            StmtKind::Assign { place, value }
        };
        out.push(Stmt::new(self.sp(e.span), assignment));
        Ok(())
    }

    fn assign_op(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        op: BinOpKind,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        let bool_bits = matches!(op, BinOpKind::BitAnd | BinOpKind::BitOr)
            && self.expr_rty_adj(lhs).is_bool()
            && self.expr_rty_adj(rhs).is_bool();
        if bool_bits && !self.cx.opts.new_mut_ref {
            // Verus reads the operator before either side.
            return Err(FnProblem::Rejected(bool_bitwise_error(op, lhs.span)));
        }
        let place = self.place(lhs)?;
        self.check_assign_target(&place, e.span, ctx)?;
        if !self.cx.opts.new_mut_ref && place.projections.iter().any(|p| *p != Projection::Deref) {
            // Without `-V new-mut-ref` Verus rewrites `x op= v` to
            // `x = x op v` only when the target is a variable, possibly
            // behind `&mut` (`ast_simplify.rs`, `ExprX::Assign`); a field
            // target is its error.
            self.errors.push(UserError::new(
                Phase::Simplify,
                lhs.span,
                messages::COMPOUND_ASSIGN_LHS,
            ));
        }
        let ty = self.expr_ty(lhs)?;
        // For primitive types Rust evaluates the right side first.
        let mut rhs_out = Vec::new();
        let rv = self.expr(rhs, ctx, &mut rhs_out)?;
        if bool_bits {
            // Under `-V new-mut-ref`, after both sides.
            return Err(FnProblem::Rejected(bool_bitwise_error(op, lhs.span)));
        }
        if !self.cx.opts.new_mut_ref && may_write_local(&rhs_out, place.local) {
            // Without `-V new-mut-ref` Verus rewrites `x op= v` to
            // `x = x op v` (`ast_simplify.rs`), reading `x` before `v`
            // runs: when `v` writes `x`, Verus's value is not Rust's.
            return refuse(
                "compound-assign-order",
                "a compound assignment whose right side may write its target",
                e.span,
            );
        }
        out.extend(rhs_out);
        let current = Expr::read(place.clone(), ty, self.sp(lhs.span));
        let overloaded = self.typeck.is_method_call(e);
        let value = self.arith_or_bits(op, current, rv, ctx, overloaded, e.span)?;
        out.push(Stmt::new(
            self.sp(e.span),
            StmtKind::Assign { place, value },
        ));
        Ok(())
    }

    // ------------------------------------------------------------------
    // Places
    // ------------------------------------------------------------------

    fn place(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Place> {
        self.attr_hook(e, false)?;
        self.no_adjustments(e)?;
        let place = self.place_unadjusted(e)?;
        self.attr_hook(e, true)?;
        Ok(place)
    }

    /// Is `e` adjusted by exactly a reborrow, `&mut *e`?
    fn is_reborrow(&self, e: &hir::Expr<'_>) -> bool {
        matches!(
            self.typeck.expr_adjustments(e),
            [
                Adjustment {
                    kind: Adjust::Deref(DerefAdjustKind::Builtin),
                    ..
                },
                Adjustment {
                    kind: Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Mut { .. })),
                    ..
                },
            ]
        )
    }

    /// The place `e` names, as written (adjustments are the caller's
    /// concern).
    fn place_unadjusted(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Place> {
        match e.kind {
            hir::ExprKind::Path(ref qpath) => match self.typeck.qpath_res(qpath, e.hir_id) {
                Res::Local(hir_id) => match self.local_ids.get(&hir_id) {
                    Some(local) => Ok(Place::local(*local)),
                    None => refuse(
                        "path",
                        "a variable captured from outside the function",
                        e.span,
                    ),
                },
                _ => refuse(
                    "place",
                    "an assignment to something that is not a variable",
                    e.span,
                ),
            },
            hir::ExprKind::Unary(hir::UnOp::Deref, inner) => {
                if !matches!(self.expr_rty(inner).kind(), ty::Ref(..)) {
                    return refuse(
                        "place",
                        "a dereference of something that is not a reference",
                        e.span,
                    );
                }
                let mut place = self.place(inner)?;
                place.projections.push(Projection::Deref);
                Ok(place)
            }
            hir::ExprKind::Field(base, _) => {
                let projection = self.field_projection(e, base)?;
                self.check_field_access(e, base);
                let mut place = self.place(base)?;
                place.projections.push(projection);
                Ok(place)
            }
            _ => refuse(
                "place",
                "an assignment target that is not a variable, field or dereference",
                e.span,
            ),
        }
    }

    /// A field expression `e` of `base` reads a struct's field: Verus's
    /// datatype access rule applies.
    fn check_field_access(&mut self, e: &hir::Expr<'_>, base: &hir::Expr<'_>) {
        if let ty::Adt(adt, _) = self.expr_rty_adj(base).kind() {
            if adt.is_struct() {
                self.check_datatype_access(*adt, e.span, "field expression");
            }
        }
    }

    /// The projection of `base.field`.
    fn field_projection(&self, e: &hir::Expr<'_>, base: &hir::Expr<'_>) -> R<Projection> {
        let index = self.typeck.field_index(e.hir_id).as_u32();
        match self.expr_rty_adj(base).kind() {
            ty::Tuple(_) => Ok(Projection::TupleField(index)),
            ty::Adt(adt, _) if adt.is_struct() => {
                if self.cx.source_opaque_nominal(adt.did()) {
                    return refuse(
                        "source-opaque-representation",
                        "an opaque source carrier has no field projection authority",
                        e.span,
                    );
                }
                if self.cx.imported_nominal(adt.did()).is_some() {
                    return refuse(
                        "opaque-import",
                        "an imported carrier has no field projection authority",
                        e.span,
                    );
                }
                Ok(Projection::Field {
                    variant: 0,
                    field: index,
                })
            }
            _ => refuse(
                "expr",
                "a field of something that is not a struct or tuple",
                e.span,
            ),
        }
    }

    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------

    /// Refuse an expression that rustc adjusts (auto-deref, auto-borrow,
    /// coercion): the reader lowers expressions as written.
    fn no_adjustments(&mut self, e: &hir::Expr<'_>) -> R<()> {
        if self.adjusting == Some(e.hir_id) {
            self.adjusting = None;
            return Ok(());
        }
        let adjusted = self
            .typeck
            .expr_adjustments(e)
            .iter()
            .any(|a| !matches!(a.kind, Adjust::NeverToAny));
        if adjusted {
            return refuse(
                "adjustment",
                "an implicit conversion (auto-deref, auto-borrow or coercion)",
                e.span,
            );
        }
        Ok(())
    }

    /// An expression of type `!` used for its value: a `return`, or a block
    /// or `if` every path through which ends in one, as in
    /// `if b { return 1; }` or `foo({ return; })`. It is lowered as
    /// statements. The value it stands for is never produced, so an
    /// uninitialized temporary of the type rustc coerces it to stands in for
    /// it; every path reaching that temporary has already returned.
    fn diverging_value(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = e.span;
        let adjusted = self.expr_rty_adj(e);
        let ty = if adjusted.is_never() {
            // Not coerced: the value is discarded (statement position).
            Ty::Unit
        } else {
            match self.vc_ty(adjusted)? {
                Some(ty) => ty,
                None => {
                    return refuse(
                        "type",
                        format!("an expression of type `!` used as `{adjusted}`"),
                        span,
                    )
                }
            }
        };
        self.diverging_stmts(e, ctx, out)?;
        if self.never_to_any(e.peel_drop_temps()) {
            self.push_unreachable(span, out);
        }
        if ty == Ty::Unit {
            return Ok(self.unit(span));
        }
        let t = self.temp(ty, ctx, span);
        out.push(Stmt::new(
            self.sp(span),
            StmtKind::Let {
                local: t,
                init: None,
            },
        ));
        Ok(self.read_local(t, span))
    }

    /// Lower `e`, of type `!`, as statements.
    fn diverging_stmts(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        match e.kind {
            hir::ExprKind::DropTemps(inner) => self.diverging_stmts(inner, ctx, out),
            // `stmt_expr` reads these without asking for their value.
            hir::ExprKind::Ret(_)
            | hir::ExprKind::Block(_, None)
            | hir::ExprKind::Loop(..)
            | hir::ExprKind::Break(..)
            | hir::ExprKind::Continue(_) => self.stmt_expr(e, ctx, out),
            hir::ExprKind::If(cond, then_expr, Some(else_expr)) => {
                if ctx == Ctx::Spec && !self.mode_rejected {
                    return refuse("effect-in-spec", "spec code with an effect", e.span);
                }
                let cond = self.expr(cond, ctx, out)?;
                let mut then_out = Vec::new();
                self.stmt_expr(then_expr, ctx, &mut then_out)?;
                let mut else_out = Vec::new();
                self.stmt_expr(else_expr, ctx, &mut else_out)?;
                out.push(Stmt::new(
                    self.sp(e.span),
                    StmtKind::If {
                        cond,
                        then_block: Block::new(then_out),
                        else_block: Block::new(else_out),
                    },
                ));
                Ok(())
            }
            hir::ExprKind::Match(scrutinee, arms, source) => self
                .ordinary_match_value(e, scrutinee, arms, source, ctx, out)
                .map(|_| ()),
            _ => refuse(
                "diverging-expr",
                format!(
                    "an expression that never produces a value ({})",
                    expr_kind_name(&e.kind)
                ),
                e.span,
            ),
        }
    }

    /// A spec expression: pure, lowered in the spec context.
    /// `e` with the adjustments rustc applied to it: a shared borrow
    /// (`&x` for a method receiver) and a dereference of a reference (`*r`
    /// for a field base or a receiver), both transparent to verification.
    /// Any other adjustment is refused.
    fn expr_adjusted(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if self.new_spec_reborrow(e, ctx) {
            return self.expr(e, ctx, out);
        }
        let adjustments = self.typeck.expr_adjustments(e);
        if adjustments
            .iter()
            .all(|a| matches!(a.kind, Adjust::NeverToAny))
        {
            return self.expr(e, ctx, out);
        }
        if adjustments.iter().any(|a| {
            !matches!(
                a.kind,
                Adjust::Deref(DerefAdjustKind::Builtin)
                    | Adjust::Borrow(AutoBorrow::Ref(AutoBorrowMutability::Not))
            )
        }) {
            return refuse(
                "adjustment",
                "an implicit conversion other than a shared borrow or a dereference",
                e.span,
            );
        }
        self.adjusting = Some(e.hir_id);
        let result = self.expr(e, ctx, out);
        self.adjusting = None;
        let mut value = result?;
        for adjustment in adjustments {
            value = match adjustment.kind {
                Adjust::Deref(_) => match value.ty.clone() {
                    Ty::MutRef(inner) => Expr::new(
                        *inner,
                        self.sp(e.span),
                        ExprKind::MutRefCurrent(Box::new(value)),
                    ),
                    Ty::Ref {
                        mutable: false,
                        inner,
                    } => self.shared_reference_value(value, *inner, ctx, e.span)?,
                    Ty::Ref { inner, .. } => self.builtin_reference_value(value, *inner, e.span)?,
                    _ => {
                        return refuse(
                            "adjustment",
                            "a dereference of something that is not a reference",
                            e.span,
                        )
                    }
                },
                _ => {
                    let ty = Ty::Ref {
                        mutable: false,
                        inner: Box::new(value.ty.clone()),
                    };
                    Expr::new(ty, self.sp(e.span), ExprKind::Borrow(Box::new(value)))
                }
            };
            if self.vc_ty(self.at(adjustment.target))?.as_ref() != Some(&value.ty) {
                return refuse(
                    "adjustment",
                    "an implicit conversion to a type VcIR does not match",
                    e.span,
                );
            }
        }
        Ok(value)
    }

    fn spec(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Expr> {
        let mut out = Vec::new();
        let value = self.expr(e, Ctx::Spec, &mut out)?;
        if !out.is_empty() && !self.mode_rejected {
            return refuse("effect-in-spec", "spec code with an effect", e.span);
        }
        Ok(value)
    }

    /// Logical checking does not turn legacy source syntax into ghost syntax.
    /// A40's Assert/Assume operand keeps the caller BodyCtxt.in_ghost. Headers
    /// and genuine ghost blocks still call `spec` with their explicit context.
    fn logical_in_syntax(&mut self, e: &'tcx hir::Expr<'tcx>, ctx: Ctx) -> R<Expr> {
        if !self.cx.legacy_functions.contains(&self.def_id) {
            return self.spec(e);
        }
        let mut effects = Vec::new();
        let value = self.expr(e, ctx, &mut effects)?;
        if !effects.is_empty() && !self.mode_rejected {
            return refuse(
                "effect-in-spec",
                "a logical legacy operand with an effect",
                e.span,
            );
        }
        Ok(value)
    }

    /// Lower `e` to a pure expression, emitting its effects into `out`.
    fn expr(&mut self, e: &'tcx hir::Expr<'tcx>, ctx: Ctx, out: &mut Vec<Stmt>) -> R<Expr> {
        if self.adjusting != Some(e.hir_id) && self.new_spec_reborrow(e, ctx) {
            let previous = self.adjusting;
            self.adjusting = Some(e.hir_id);
            let result = self.expr(e, ctx, out);
            self.adjusting = previous;
            let value = result?;
            if self.vc_ty(self.expr_rty_adj(e))?.as_ref() != Some(&value.ty) {
                return refuse(
                    "new-mut-ref",
                    "a Spec reborrow changed its logical carrier type",
                    e.span,
                );
            }
            return Ok(value);
        }
        self.attr_hook(e, false)?;
        let value = self.expr_unhooked(e, ctx, out)?;
        self.attr_hook(e, true)?;
        self.trigger_attrs(e, &value);
        Ok(value)
    }

    /// The actual compiler's exact implicit reborrow, interpreted as a Spec
    /// read only in a pure Spec function. Explicit borrows and every runtime
    /// storage use retain their separate availability/ownership requirements.
    fn new_spec_reborrow(&self, e: &hir::Expr<'_>, ctx: Ctx) -> bool {
        self.cx.opts.new_mut_ref
            && self.mode == Mode::Spec
            && ctx == Ctx::Spec
            && self.is_reborrow(e)
            && matches!(self.expr_rty(e).kind(), ty::Ref(_, _, m) if m.is_mut())
            && self.tcx.erase_and_anonymize_regions(self.expr_rty(e))
                == self.tcx.erase_and_anonymize_regions(self.expr_rty_adj(e))
    }

    fn expr_unhooked(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if super::modes::is_proof_in_spec(self.tcx, e) {
            return self.proof_in_spec_expr(e);
        }
        if self.is_ghost_block(e) {
            return self.ghost_block_value(e, ctx, out);
        }
        self.no_adjustments(e)?;
        let span = e.span;
        if self.reading_initializer
            && matches!(
                e.kind,
                hir::ExprKind::Call(..) | hir::ExprKind::MethodCall(..)
            )
        {
            if self.mode_rejected {
                // A current registered const-fn occurrence can surface the
                // existing typed missing-Modes denial. Only the original
                // actual mode error may then take precedence. No call is
                // lowered: None/Some both retain the refusal below, and
                // other native selection/availability errors remain hard.
                let _ = self.checked_constant_use(e)?;
            }
            return refuse(
                "constant-initializer",
                "a function call in a dual constant initializer",
                span,
            );
        }
        if self.expr_rty(e).is_never() {
            return self.diverging_value(e, ctx, out);
        }
        match e.kind {
            hir::ExprKind::DropTemps(inner) => self.expr(inner, ctx, out),
            hir::ExprKind::Lit(lit) => self.literal(e, &lit.node, false),
            hir::ExprKind::Path(ref qpath) => self.path_expr(e, qpath, ctx, out),
            hir::ExprKind::Unary(op, arg) => self.unary(e, op, arg, ctx, out),
            hir::ExprKind::Binary(op, lhs, rhs) => self.binary(e, op.node, lhs, rhs, ctx, out),
            hir::ExprKind::Call(func, args) => self.call(e, func, args, ctx, out, false),
            hir::ExprKind::MethodCall(_, receiver, args, _) => {
                let Some(def_id) = self.typeck.type_dependent_def_id(e.hir_id) else {
                    return refuse("method-call", "an unresolved method call", span);
                };
                let mut all = vec![receiver];
                all.extend(args.iter());
                match self.cx.verus_item(def_id) {
                    Some(item) => self.marker(e, item, def_id, &all, ctx, out),
                    None => {
                        let generic_args = self.typeck.node_args(e.hir_id);
                        self.call_fn(e, def_id, generic_args, &all, ctx, out, false)
                    }
                }
            }
            hir::ExprKind::Block(block, None) => {
                if self.reading_initializer {
                    return self.initializer_block(block.stmts, block.expr, block.span);
                }
                if ctx == Ctx::Spec {
                    return self.spec_block(block.stmts, block.expr, block.span, false);
                }
                for stmt in block.stmts {
                    self.stmt(stmt, ctx, out)?;
                }
                match block.expr {
                    Some(tail) => self.expr(tail, ctx, out),
                    None => Ok(self.unit(span)),
                }
            }
            hir::ExprKind::If(cond, then_expr, else_expr) => {
                if self.reading_initializer {
                    let Some(other) = else_expr else {
                        return refuse(
                            "constant-initializer",
                            "an initializer if without an else value",
                            span,
                        );
                    };
                    return Ok(Expr::new(
                        self.expr_ty(e)?,
                        self.sp(span),
                        ExprKind::If {
                            cond: Box::new(self.expr(cond, ctx, out)?),
                            then_expr: Box::new(self.expr(then_expr, ctx, out)?),
                            else_expr: Box::new(self.expr(other, ctx, out)?),
                        },
                    ));
                }
                self.if_expr(e, cond, then_expr, else_expr, ctx, out)
            }
            hir::ExprKind::Match(scrutinee, arms, source) => {
                self.ordinary_match_value(e, scrutinee, arms, source, ctx, out)
            }
            hir::ExprKind::Struct(qpath, fields, tail) => {
                self.struct_expr(e, qpath, fields, tail, ctx, out)
            }
            hir::ExprKind::Field(base, _) => {
                let projection = self.field_projection(e, base)?;
                self.check_field_access(e, base);
                let base = self.expr_adjusted(base, ctx, out)?;
                let ty = self.expr_ty(e)?;
                let kind = match projection {
                    Projection::Field { variant, field } => ExprKind::Field {
                        base: Box::new(base),
                        variant,
                        field,
                    },
                    Projection::TupleField(index) => ExprKind::TupleField {
                        base: Box::new(base),
                        index,
                    },
                    Projection::Deref => {
                        return refuse("expr", "a field through a reference", span)
                    }
                };
                Ok(Expr::new(ty, self.sp(span), kind))
            }
            hir::ExprKind::Tup(elems) => {
                if elems.is_empty() {
                    return Ok(self.unit(span));
                }
                let ty = self.expr_ty(e)?;
                let elems: Vec<&'tcx hir::Expr<'tcx>> = elems.iter().collect();
                let values = self.operands(&elems, ctx, out)?;
                Ok(Expr::new(ty, self.sp(span), ExprKind::Tuple(values)))
            }
            hir::ExprKind::Cast(inner, _) => {
                let value = self.expr(inner, ctx, out)?;
                let to = self.expr_ty(e)?;
                self.scalar_cast(inner, value, to, ctx, span)
            }
            hir::ExprKind::Assign(lhs, _, _) | hir::ExprKind::AssignOp(_, lhs, _) => {
                self.assignment_value(e, lhs, ctx, out)
            }
            hir::ExprKind::Loop(..) => {
                self.stmt_expr(e, ctx, out)?;
                Ok(self.unit(span))
            }
            hir::ExprKind::AddrOf(hir::BorrowKind::Ref, rustc_ast::Mutability::Not, inner) => {
                let value = self.expr(inner, ctx, out)?;
                let ty = Ty::Ref {
                    mutable: false,
                    inner: Box::new(value.ty.clone()),
                };
                Ok(Expr::new(
                    ty,
                    self.sp(span),
                    ExprKind::Borrow(Box::new(value)),
                ))
            }
            hir::ExprKind::Closure(_) => refuse("closure", "closures are not read yet", span),
            hir::ExprKind::Let(_) => {
                refuse("if-let", "`if let` / `let` chains are not read yet", span)
            }
            _ => refuse("expr", expr_kind_name(&e.kind), span),
        }
    }

    /// A Boolean-to-integer or explicit integer cast. Keep each integer clip
    /// boundary even when the source range fits: the isolated BV language
    /// distinguishes an explicit `as nat` clip from a mathematical coercion.
    fn int_cast(&self, value: Expr, to: Ty, span: Span) -> R<Expr> {
        if value.ty == Ty::Bool && to.int_range().is_some_and(|range| range != IntRange::Char) {
            // Rust and Verus map false/true to 0/1 in the destination type.
            // Keep the already-read operand exactly once, including its modes
            // and effects; the ordinary conditional lowering checks it.
            let at = self.sp(span);
            let one = Expr::int_lit(1, to.clone(), at);
            let zero = Expr::int_lit(0, to.clone(), at);
            return Ok(Expr::new(
                to,
                at,
                ExprKind::If {
                    cond: Box::new(value),
                    then_expr: Box::new(one),
                    else_expr: Box::new(zero),
                },
            ));
        }
        let (Some(from_range), Some(to_range)) = (value.ty.int_range(), to.int_range()) else {
            return refuse("expr", "a cast that is not between integer types", span);
        };
        let _ = from_range;
        let kind = if to_range == IntRange::Int {
            CastKind::Exact
        } else {
            CastKind::As
        };
        Ok(value.cast(kind, to, self.sp(span)))
    }

    fn literal(&self, e: &hir::Expr<'_>, lit: &AstLitKind, negate: bool) -> R<Expr> {
        let span = e.span;
        match *lit {
            AstLitKind::Bool(b) if !negate => Ok(Expr::bool_lit(b, self.sp(span))),
            AstLitKind::Int(value, _) => {
                let ty = self.expr_ty(e)?;
                if ty.int_range().is_none() {
                    return refuse("literal", "an integer literal of a non-integer type", span);
                }
                let magnitude = value.get();
                check_lit_int(span, negate, magnitude, &ty, self.cx.architecture)?;
                let lit = IntLit {
                    negative: negate && magnitude != 0,
                    magnitude,
                };
                Ok(Expr::new(ty, self.sp(span), ExprKind::Lit(Lit::Int(lit))))
            }
            _ => refuse(
                "literal",
                "a literal that is not a boolean or an integer",
                span,
            ),
        }
    }

    fn path_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        qpath: &'tcx QPath<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        match self.typeck.qpath_res(qpath, e.hir_id) {
            Res::Def(DefKind::AssocConst, definition)
                if super::architecture::integer_constant(self.tcx, definition).is_some() =>
            {
                let value = super::architecture::integer_constant(self.tcx, definition)
                    .ok_or_else(|| {
                        FnProblem::Refused(Refusal::new(
                            "integer-bound",
                            "the native primitive identity changed",
                            e.span,
                        ))
                    })?;
                Ok(Expr::new(
                    self.expr_ty(e)?,
                    self.sp(e.span),
                    ExprKind::IntegerConstant(value),
                ))
            }
            Res::Def(DefKind::Const | DefKind::AssocConst | DefKind::Static { .. }, def)
                if def.as_local().is_some_and(|local| {
                    matches!(
                        self.cx.constants.value_kind(local),
                        Some(FnKind::Constant(ConstMode::Exec) | FnKind::Static)
                    )
                }) =>
            {
                let selected = self.checked_constant_use(e)?.ok_or_else(|| {
                    FnProblem::Refused(Refusal::new(
                        "constant-use",
                        "the value lacks its native read selection",
                        e.span,
                    ))
                })?;
                if selected.original != def {
                    return refuse("constant-use", "the value read changed definition", e.span);
                }
                // Only the exact original declaration's postcondition names
                // its checked result. This creates neither a read nor a global
                // hypothesis while proving that same initializer.
                if self.area == Area::Ensures && selected.declaration == self.def_id {
                    let value = self.read_local(self.ret, e.span);
                    if value.ty != self.expr_ty(e)? {
                        return refuse(
                            "constant-use",
                            "the initializer postcondition result changed type",
                            e.span,
                        );
                    }
                    return Ok(value);
                }
                if ctx != Ctx::Exec && !self.mode_rejected {
                    return refuse(
                        "constant-use",
                        "an executable value read in ghost code",
                        e.span,
                    );
                }
                self.check_function_access(def, e.span);
                let target =
                    self.call_target(selected.declaration.to_def_id(), selected.arguments, e.span)?;
                self.emit_value_call(e, target, out)
            }
            Res::Def(DefKind::Const | DefKind::AssocConst, def)
                if def
                    .as_local()
                    .is_some_and(|local| self.cx.constants.declaration(local).is_some()) =>
            {
                let declaration = self
                    .cx
                    .constants
                    .declaration(def.expect_local())
                    .expect("registered constant");
                self.check_function_access(def, e.span);
                let target = self.call_target(
                    declaration.to_def_id(),
                    self.typeck.node_args(e.hir_id),
                    e.span,
                )?;
                Ok(Expr::new(
                    self.expr_ty(e)?,
                    self.sp(e.span),
                    ExprKind::Call {
                        callee: target.id,
                        type_args: target.type_args,
                        args: Vec::new(),
                    },
                ))
            }
            Res::Local(hir_id) => match self.local_ids.get(&hir_id) {
                Some(local) => Ok(self.read_local(*local, e.span)),
                None => refuse(
                    "path",
                    "a variable captured from outside the function",
                    e.span,
                ),
            },
            Res::Def(DefKind::Ctor(_, CtorKind::Const), constructor) => {
                let ty::Adt(native_adt, _) = self.expr_rty(e).kind() else {
                    return refuse("type", "a unit constructor of a non-ADT type", e.span);
                };
                let Some((variant_index, variant)) = super::datatypes::constructor_variant(
                    *native_adt,
                    Res::Def(self.tcx.def_kind(constructor), constructor),
                ) else {
                    return refuse(
                        "adt",
                        "a unit constructor outside its actual native datatype",
                        e.span,
                    );
                };
                if !variant.fields.is_empty() {
                    return refuse("adt", "a unit constructor with native fields", e.span);
                }
                if let ty::Adt(adt, _) = self.expr_rty(e).kind() {
                    if self.cx.source_opaque_nominal(adt.did()) {
                        return refuse(
                            "source-opaque-representation",
                            "an opaque source carrier has no unit constructor authority",
                            e.span,
                        );
                    }
                    if self.cx.imported_nominal(adt.did()).is_some() {
                        return refuse(
                            "opaque-import",
                            "an imported carrier has no unit constructor authority",
                            e.span,
                        );
                    }
                    self.check_datatype_access(*adt, e.span, "constructor");
                }
                let ty = self.expr_ty(e)?;
                let Ty::Adt(adt, _) = ty else {
                    return refuse("type", "a unit struct VcIR does not know", e.span);
                };
                Ok(Expr::new(
                    ty,
                    self.sp(e.span),
                    ExprKind::Ctor {
                        adt,
                        variant: variant_index,
                        fields: Vec::new(),
                    },
                ))
            }
            res => refuse("path", format!("a path to {}", res.descr()), e.span),
        }
    }

    fn unary(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        op: hir::UnOp,
        arg: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = e.span;
        match op {
            hir::UnOp::Deref => {
                // `final_` has no first-class value semantics: only its
                // immediately enclosing `*` denotes the future projection.
                if let hir::ExprKind::Call(func, [inner]) = arg.kind {
                    if matches!(self.callee_item(func), Some((VerusItem::Final, _))) {
                        if !self.cx.opts.new_mut_ref || ctx == Ctx::Exec {
                            return refuse(
                                "new-mut-ref",
                                "`*final_` requires ghost code under -V new-mut-ref",
                                span,
                            );
                        }
                        let reference = self.mut_ref_intrinsic_arg(inner, ctx, out)?;
                        let Ty::MutRef(referent) = &reference.ty else {
                            return refuse(
                                "new-mut-ref",
                                "`final_` expects an opaque mutable reference",
                                arg.span,
                            );
                        };
                        let result = self.expr_ty(e)?;
                        if referent.as_ref() != &result {
                            return refuse(
                                "new-mut-ref",
                                "`final_` changed its native referent type",
                                arg.span,
                            );
                        }
                        return Ok(Expr::new(
                            result,
                            self.sp(span),
                            ExprKind::MutRefFuture(Box::new(reference)),
                        ));
                    }
                }
                // `*old(x)`: the entry value behind a `&mut` parameter.
                if let hir::ExprKind::Call(func, [inner]) = arg.kind {
                    if matches!(self.callee_item(func), Some((VerusItem::Old, _))) {
                        // `old` takes `&mut A`; passing a `&mut` parameter
                        // reborrows it (`&mut *x`), which names the same place.
                        if !self.is_reborrow(inner) {
                            self.no_adjustments(inner)?;
                        }
                        let mut place = self.place_unadjusted(inner)?;
                        place.projections.push(Projection::Deref);
                        let ty = self.expr_ty(e)?;
                        return Ok(Expr::new(ty, self.sp(span), ExprKind::Old(place)));
                    }
                }
                if self.cx.opts.new_mut_ref
                    && matches!(self.expr_rty_adj(arg).kind(), ty::Ref(_, _, m) if m.is_mut())
                {
                    let reference = self.expr(arg, ctx, out)?;
                    if let Ty::MutRef(inner) = reference.ty.clone() {
                        return Ok(Expr::new(
                            *inner,
                            self.sp(span),
                            ExprKind::MutRefCurrent(Box::new(reference)),
                        ));
                    }
                }
                if matches!(self.expr_rty_adj(arg).kind(), ty::Ref(_, _, m) if !m.is_mut()) {
                    let value = self.expr_adjusted(arg, ctx, out)?;
                    let result = self.expr_ty(e)?;
                    return self.shared_reference_value(value, result, ctx, span);
                }
                let place = self.place(e)?;
                let ty = self.expr_ty(e)?;
                Ok(Expr::read(place, ty, self.sp(span)))
            }
            hir::UnOp::Not => {
                let value = self.expr(arg, ctx, out)?;
                let ok =
                    value.ty == Ty::Bool || value.ty.int_range().is_some_and(|r| r.is_bounded());
                if !ok {
                    return refuse(
                        "expr",
                        "`!` on something that is not a bool or a machine integer",
                        span,
                    );
                }
                // Expr::not is Boolean logical negation. Native integer !
                // keeps its actual type and width for WF and BV lowering.
                let ty = self.expr_ty(e)?;
                Ok(Expr::new(
                    ty,
                    self.sp(span),
                    ExprKind::Unary {
                        op: UnOp::Not,
                        arg: Box::new(value),
                        check: None,
                    },
                ))
            }
            hir::UnOp::Neg => {
                if let hir::ExprKind::Lit(lit) = arg.kind {
                    if matches!(lit.node, AstLitKind::Int(..))
                        && self.typeck.expr_adjustments(arg).is_empty()
                    {
                        return self.literal(arg, &lit.node, true).map(|mut l| {
                            l.span = self.sp(span);
                            l
                        });
                    }
                }
                let value = self.expr(arg, ctx, out)?;
                let ty = self.expr_ty(e)?;
                let range = value.ty.int_range();
                match range {
                    Some(r) if r.is_math() => Ok(Expr::new(
                        Ty::int(),
                        self.sp(span),
                        ExprKind::Unary {
                            op: UnOp::Neg,
                            arg: Box::new(self.to_int(value)),
                            check: None,
                        },
                    )),
                    Some(r) if r.is_signed_machine() && !ctx.ghost() => {
                        let site = self.site();
                        Ok(Expr::new(
                            ty,
                            self.sp(span),
                            ExprKind::Unary {
                                op: UnOp::Neg,
                                arg: Box::new(value),
                                check: Some(site),
                            },
                        ))
                    }
                    Some(r) if r.is_signed_machine() => {
                        // Ghost negation wraps into the type.
                        let exact = Expr::new(
                            Ty::int(),
                            self.sp(span),
                            ExprKind::Unary {
                                op: UnOp::Neg,
                                arg: Box::new(self.to_int(value)),
                                check: None,
                            },
                        );
                        Ok(exact.cast(CastKind::As, ty, self.sp(span)))
                    }
                    _ => refuse(
                        "expr",
                        "negation of something that is not a signed or math integer",
                        span,
                    ),
                }
            }
        }
    }

    fn binary(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        op: BinOpKind,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = e.span;
        if matches!(op, BinOpKind::Eq | BinOpKind::Ne)
            && (self.cx.mentions_source_opaque(self.expr_rty_adj(lhs))
                || self.cx.mentions_source_opaque(self.expr_rty_adj(rhs)))
        {
            return refuse(
                "source-opaque-representation",
                "opaque source equality requires its own semantic consumer",
                span,
            );
        }
        match op {
            BinOpKind::BitAnd | BinOpKind::BitOr
                if self.expr_rty_adj(lhs).is_bool() && self.expr_rty_adj(rhs).is_bool() =>
            {
                // Verus builds both operands before it looks at the
                // operator, so their errors come first.
                self.operand_pair(lhs, rhs, ctx, out)?;
                Err(FnProblem::Rejected(bool_bitwise_error(op, lhs.span)))
            }
            BinOpKind::And | BinOpKind::Or => {
                let lv = self.expr(lhs, ctx, out)?;
                self.short_circuit(op == BinOpKind::And, lv, rhs, span, ctx, out)
            }
            BinOpKind::Eq
            | BinOpKind::Ne
            | BinOpKind::Lt
            | BinOpKind::Le
            | BinOpKind::Gt
            | BinOpKind::Ge => {
                let (lv, rv) = self.operand_pair(lhs, rhs, ctx, out)?;
                let vop = match op {
                    BinOpKind::Eq => BinOp::Eq,
                    BinOpKind::Ne => BinOp::Ne,
                    BinOpKind::Lt => BinOp::Lt,
                    BinOpKind::Le => BinOp::Le,
                    BinOpKind::Gt => BinOp::Gt,
                    _ => BinOp::Ge,
                };
                self.comparison(vop, lv, rv, span)
            }
            _ => {
                let (lv, rv) = self.operand_pair(lhs, rhs, ctx, out)?;
                let overloaded = self.typeck.is_method_call(e);
                self.arith_or_bits(op, lv, rv, ctx, overloaded, span)
            }
        }
    }

    /// `==`, `!=`, `<`, ... on two values: integers of different types are
    /// compared as `int`; other operands must have one type.
    fn comparison(&self, op: BinOp, lv: Expr, rv: Expr, span: Span) -> R<Expr> {
        let ints = lv.ty.int_range().is_some() && rv.ty.int_range().is_some();
        let (lv, rv) = if ints {
            self.unify_ints(lv, rv)
        } else {
            if lv.ty != rv.ty {
                return refuse("expr", "a comparison of values of different types", span);
            }
            if !matches!(op, BinOp::Eq | BinOp::Ne) {
                return refuse("expr", "an ordering comparison of non-integers", span);
            }
            (lv, rv)
        };
        Ok(Expr::binary(op, lv, rv, Ty::Bool, self.sp(span)))
    }

    /// `a && b`, `a || b`: pure when `b` has no effects, otherwise an `if`
    /// over a temporary.
    fn short_circuit(
        &mut self,
        is_and: bool,
        lv: Expr,
        rhs: &'tcx hir::Expr<'tcx>,
        span: Span,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let mut rhs_out = Vec::new();
        let rv = self.expr(rhs, ctx, &mut rhs_out)?;
        if rhs_out.is_empty() {
            let op = if is_and { BinOp::And } else { BinOp::Or };
            return Ok(Expr::binary(op, lv, rv, Ty::Bool, self.sp(span)));
        }
        self.short_circuit_with(is_and, lv, rv, rhs_out, span, ctx, out)
    }

    /// `+ - * / %` and `& | ^` on two values of one type.
    fn arith_or_bits(
        &mut self,
        op: BinOpKind,
        lv: Expr,
        rv: Expr,
        ctx: Ctx,
        overloaded: bool,
        span: Span,
    ) -> R<Expr> {
        let arith = match op {
            BinOpKind::Add => Some(BinOp::Add),
            BinOpKind::Sub => Some(BinOp::Sub),
            BinOpKind::Mul => Some(BinOp::Mul),
            BinOpKind::Div => Some(BinOp::Div),
            BinOpKind::Rem => Some(BinOp::Rem),
            _ => None,
        };
        if let Some(vop) = arith {
            if lv.ty != rv.ty {
                return refuse(
                    "arith-type",
                    "arithmetic on operands of different types",
                    span,
                );
            }
            let ty = lv.ty.clone();
            let Some(range) = ty.int_range() else {
                return refuse("arith-type", "arithmetic on a non-integer type", span);
            };
            if range.is_math() {
                // `int`/`nat` operators (Rust impls in verus_builtin): exact.
                if !overloaded || (range == trust_vc_vcir::IntRange::Nat && vop == BinOp::Sub) {
                    return refuse("arith-type", "subtraction on `nat` in exec code", span);
                }
                return Ok(Expr::binary(vop, lv, rv, ty, self.sp(span)));
            }
            return Ok(self.machine_arith(vop, lv, rv, ty, ctx, span));
        }
        let bits = match op {
            BinOpKind::BitAnd => BinOp::BitAnd,
            BinOpKind::BitOr => BinOp::BitOr,
            BinOpKind::BitXor => BinOp::BitXor,
            BinOpKind::Shl => BinOp::Shl,
            BinOpKind::Shr => BinOp::Shr,
            _ => return refuse("expr", format!("operator `{}`", op.as_str()), span),
        };
        if matches!(bits, BinOp::Shl | BinOp::Shr) {
            if ctx == Ctx::Exec {
                return refuse(
                    "shift",
                    "an exec shift requiring a width overflow check",
                    span,
                );
            }
            if !lv.ty.int_range().is_some_and(|range| range.is_bounded())
                || rv.ty.int_range().is_none()
            {
                return refuse(
                    "shift",
                    "a shift without finite left width and integer count",
                    span,
                );
            }
            let ty = lv.ty.clone();
            return Ok(Expr::binary(bits, lv, rv, ty, self.sp(span)));
        }
        let ok = lv.ty == rv.ty
            && (lv.ty == Ty::Bool || lv.ty.int_range().is_some_and(|r| r.is_bounded()));
        if !ok {
            return refuse(
                "arith-type",
                "a bitwise operator on unsupported operands",
                span,
            );
        }
        let ty = lv.ty.clone();
        Ok(Expr::binary(bits, lv, rv, ty, self.sp(span)))
    }

    /// Arithmetic on a machine integer type: checked in exec code, wrapping
    /// into the type in ghost code.
    fn machine_arith(
        &mut self,
        op: BinOp,
        lv: Expr,
        rv: Expr,
        ty: Ty,
        ctx: Ctx,
        span: Span,
    ) -> Expr {
        if ctx.ghost() {
            let exact = Expr::binary(
                op,
                self.to_int(lv),
                self.to_int(rv),
                Ty::int(),
                self.sp(span),
            );
            exact.cast(CastKind::As, ty, self.sp(span))
        } else {
            let site = self.site();
            Expr::checked_binary(op, lv, rv, ty, site, self.sp(span))
        }
    }

    fn if_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        cond: &'tcx hir::Expr<'tcx>,
        then_expr: &'tcx hir::Expr<'tcx>,
        else_expr: Option<&'tcx hir::Expr<'tcx>>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = e.span;
        let spec_condition = self.legacy_spec_condition(cond, ctx)?;
        let cond = self.expr(cond, ctx, out)?;
        let ty = self.expr_ty(e)?;
        let mut then_out = Vec::new();
        let tv = self.expr_adjusted(then_expr, ctx, &mut then_out)?;
        let mut else_out = Vec::new();
        let ev = match else_expr {
            Some(else_expr) => self.expr_adjusted(else_expr, ctx, &mut else_out)?,
            None => self.unit(span),
        };
        let sid = self.sp(span);
        if then_out.is_empty() && else_out.is_empty() {
            // Unit values still carry the condition's prophetic effect.
            // Only statement position discards that effect.
            return Ok(Expr::new(
                ty,
                sid,
                ExprKind::If {
                    cond: Box::new(cond),
                    then_expr: Box::new(tv),
                    else_expr: Box::new(ev),
                },
            ));
        }
        if ctx == Ctx::Spec && !self.mode_rejected {
            return refuse("effect-in-spec", "spec code with an effect", span);
        }
        // Branches with effects use a value temporary, including Unit:
        // control and arm effects must reach a value consumer.
        let result = {
            let mode = self.legacy_result_mode(e, &ty, ctx)?;
            let t = self.temp_with_mode(ty.clone(), mode, span);
            if self.locals[t.index()].mode == Mode::Spec {
                // This generated expression result is initialized by both
                // arms. The flow checker joins their effects and the guard.
                self.locals[t.index()].prophecy = DeclProphecy::DelayedInfer;
            }
            out.push(Stmt::new(
                sid,
                StmtKind::Let {
                    local: t,
                    init: None,
                },
            ));
            let (tv, ev) = if mode == Mode::Spec {
                let tv = self.legacy_branch_value(then_expr, tv, ctx, &mut then_out)?;
                let ev = match else_expr {
                    Some(source) => self.legacy_branch_value(source, ev, ctx, &mut else_out)?,
                    None => ev,
                };
                (tv, ev)
            } else {
                (tv, ev)
            };
            then_out.push(Stmt::new(
                sid,
                StmtKind::Assign {
                    place: Place::local(t),
                    value: tv,
                },
            ));
            else_out.push(Stmt::new(
                sid,
                StmtKind::Assign {
                    place: Place::local(t),
                    value: ev,
                },
            ));
            Some(t)
        };
        let then_block = Block::new(then_out);
        let else_block = Block::new(else_out);
        let conditional = if spec_condition {
            StmtKind::IfSpec {
                cond,
                then_block,
                else_block,
            }
        } else {
            StmtKind::If {
                cond,
                then_block,
                else_block,
            }
        };
        out.push(Stmt::new(sid, conditional));
        Ok(match result {
            Some(t) => self.read_local(t, span),
            None => self.unit(span),
        })
    }

    /// Struct-only consumers retain their existing pattern/BV boundary.
    fn is_struct_ctor(&self, func: &hir::Expr<'_>) -> bool {
        let hir::ExprKind::Path(qpath) = &func.kind else {
            return false;
        };
        matches!(
            self.typeck.qpath_res(qpath, func.hir_id),
            Res::Def(DefKind::Ctor(CtorOf::Struct, CtorKind::Fn), _)
        )
    }

    /// Is `func` an actual tuple struct or tuple variant constructor?
    fn is_adt_ctor(&self, func: &hir::Expr<'_>) -> bool {
        let hir::ExprKind::Path(qpath) = &func.kind else {
            return false;
        };
        matches!(
            self.typeck.qpath_res(qpath, func.hir_id),
            Res::Def(DefKind::Ctor(_, CtorKind::Fn), _)
        )
    }

    /// A native tuple constructor applied to its fields, in
    /// order (`ExprX::Ctor`).
    fn tuple_struct_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        function: &'tcx hir::Expr<'tcx>,
        args: &'tcx [hir::Expr<'tcx>],
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = e.span;
        let ty = self.expr_ty(e)?;
        let Ty::Adt(adt, _) = ty else {
            return refuse(
                "type",
                "a struct constructor of a type VcIR does not know",
                span,
            );
        };
        let ty::Adt(adt_def, _) = self.expr_rty(e).kind() else {
            return refuse("expr", "a struct constructor of a non-ADT type", span);
        };
        if self.cx.source_opaque_nominal(adt_def.did()) {
            return refuse(
                "source-opaque-representation",
                "an opaque source carrier has no tuple constructor authority",
                span,
            );
        }
        if self.cx.imported_nominal(adt_def.did()).is_some() {
            return refuse(
                "opaque-import",
                "an imported carrier has no constructor authority",
                span,
            );
        }
        let hir::ExprKind::Path(qpath) = &function.kind else {
            return refuse("adt", "a constructor without its native path", span);
        };
        let Some((variant_index, variant)) = super::datatypes::constructor_variant(
            *adt_def,
            self.typeck.qpath_res(qpath, function.hir_id),
        ) else {
            return refuse(
                "adt",
                "a constructor outside its actual native datatype",
                span,
            );
        };
        if variant.fields.len() != args.len() {
            return refuse(
                "adt",
                "a constructor with different native field arity",
                span,
            );
        }
        self.check_datatype_access(*adt_def, span, "constructor");
        let args: Vec<&'tcx hir::Expr<'tcx>> = args.iter().collect();
        let modes = variant
            .fields
            .iter()
            .map(|field| {
                super::datatypes::field_mode(self.tcx, field, span).map_err(FnProblem::Refused)
            })
            .collect::<R<Vec<_>>>()?;
        let values = self.constructor_operands(&args, &modes, ctx, out)?;
        Ok(Expr::new(
            ty,
            self.sp(span),
            ExprKind::Ctor {
                adt,
                variant: variant_index,
                fields: values,
            },
        ))
    }

    /// A spec block: `let`s and a value, as nested spec `let`s. `body` is
    /// set for the body of a spec function, whose missing value
    /// [`Self::spec_fn_body`] reports; anywhere else a block without a value
    /// is refused.
    fn spec_block(
        &mut self,
        stmts: &'tcx [hir::Stmt<'tcx>],
        tail: Option<&'tcx hir::Expr<'tcx>>,
        span: Span,
        body: bool,
    ) -> R<Expr> {
        if tail.is_none() && !body {
            return refuse("expr", "a block without a value in spec code", span);
        }
        let mut bindings = Vec::new();
        for stmt in stmts {
            // A `proof { .. }` block: evaluated before what follows it.
            if let hir::StmtKind::Semi(e) | hir::StmtKind::Expr(e) = stmt.kind {
                if super::modes::is_proof_in_spec(self.tcx, e) {
                    let value = self.proof_in_spec_expr(e)?;
                    let id = self.add_local(
                        self.local_decl(
                            "_proof",
                            Ty::Unit,
                            Mode::Spec,
                            false,
                            LocalKind::Bound,
                            e.span,
                        ),
                        true,
                    );
                    bindings.push((id, value, stmt.span));
                    continue;
                }
            }
            let hir::StmtKind::Let(local) = stmt.kind else {
                return refuse("expr", "a statement inside spec code", stmt.span);
            };
            let (Some(init), None) = (local.init, local.els) else {
                return refuse(
                    "let-pattern",
                    "a spec let without an initializer",
                    local.span,
                );
            };
            // `let ghost` is `#[verus::internal(spec)]`, `let tracked` is
            // `#[verus::internal(proof)]`. In spec code an exec `let` is a
            // spec one, and a proof `let` is an error (`modes.rs`,
            // `StmtX::Decl`), which Verus reports at the pattern. The first
            // mode attribute counts (`get_var_mode`).
            let mut declared = None;
            for (attr, attr_span) in attrs::verus_attrs(self.tcx.hir_attrs(local.hir_id)) {
                match attr {
                    VerusAttr::Mode(mode) => {
                        declared.get_or_insert(mode);
                    }
                    VerusAttr::Prophetic | VerusAttr::LetMarker(_) => {}
                    other => {
                        return refuse("attribute", format!("{other:?} on a spec let"), attr_span)
                    }
                }
            }
            if declared == Some(Mode::Proof) {
                self.errors.push(UserError::new(
                    Phase::Modes,
                    local.pat.span,
                    messages::pattern_mode(Mode::Proof.name()),
                ));
            }
            if Self::has_struct_pattern(local.pat) {
                self.local_struct_source(init, "let-pattern")?;
            }
            let value = self.spec(init)?;
            bindings.extend(self.spec_value_bindings(local.pat, value, local.span)?);
            let original_mode = declared.unwrap_or(if self.mode == Mode::Proof {
                Mode::Spec
            } else {
                self.mode
            });
            let prophecy = attrs::local_prophecy(self.tcx.hir_attrs(local.hir_id), original_mode);
            self.pattern_prophecy(local.pat, prophecy);
        }
        let mut body = match tail {
            Some(tail) => self.spec(tail)?,
            None => self.unit(span),
        };
        for (local, value, let_span) in bindings.into_iter().rev() {
            body = Expr::new(
                body.ty.clone(),
                self.sp(let_span),
                ExprKind::Let {
                    local,
                    value: Box::new(value),
                    body: Box::new(body),
                },
            );
        }
        Ok(body)
    }

    // ------------------------------------------------------------------
    // Calls
    // ------------------------------------------------------------------

    /// A call. `discard` is set when the value is not used.
    fn call(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        func: &'tcx hir::Expr<'tcx>,
        args: &'tcx [hir::Expr<'tcx>],
        ctx: Ctx,
        out: &mut Vec<Stmt>,
        discard: bool,
    ) -> R<Expr> {
        let span = e.span;
        if self.is_adt_ctor(func) {
            return self.tuple_struct_expr(e, func, args, ctx, out);
        }
        let Some(def_id) = self.callee_def_id(func) else {
            return refuse(
                "call-target",
                "a call of something that is not a named function",
                span,
            );
        };
        let args: Vec<&'tcx hir::Expr<'tcx>> = args.iter().collect();
        if let Some(item) = self.cx.verus_item(def_id) {
            return self.marker(e, item, def_id, &args, ctx, out);
        }
        let generic_args = self.typeck.node_args(func.hir_id);
        self.call_fn(e, def_id, generic_args, &args, ctx, out, discard)
    }

    /// A call of the function `def_id` at `generic_args` (as the
    /// type-check results give them) with the arguments `args`, a method
    /// call's receiver first.
    #[allow(clippy::too_many_arguments)]
    fn call_fn(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        def_id: DefId,
        generic_args: ty::GenericArgs<'tcx>,
        args: &[&'tcx hir::Expr<'tcx>],
        ctx: Ctx,
        out: &mut Vec<Stmt>,
        discard: bool,
    ) -> R<Expr> {
        let span = e.span;
        if let Some(problem) = self.enum_diagnostic_call(def_id, span) {
            return Err(problem);
        }
        let constant = self.checked_constant_use(e)?;
        let autospec = if ctx != Ctx::Exec {
            self.cx
                .autospec
                .call(self.cx, self.body_def, self.typeck, e)
                .map_err(FnProblem::Refused)?
        } else {
            None
        };
        if autospec
            .as_ref()
            .is_some_and(|call| !call.matches_constant(constant.as_ref()))
        {
            return refuse(
                "constant-use",
                "the native constant and autospec selections do not share one source",
                span,
            );
        }
        let (def_id, generic_args) = if let Some(call) = autospec {
            let refuse = |reason| FnProblem::Refused(Refusal::new("autospec-modes", reason, span));
            let facts = self
                .checked_modes
                .clone()
                .ok_or_else(|| refuse("redirection lacks the completed original mode walk"))?;
            let canonical = || {
                self.cx
                    .checked_modes
                    .borrow()
                    .get(&self.def_id)
                    .is_some_and(|actual| std::rc::Rc::ptr_eq(actual, &facts))
            };
            if call.original != def_id
                || call.original_args != generic_args
                || !canonical()
                || !facts
                    .autospec_calls
                    .get(&e.hir_id)
                    .is_some_and(|observed| observed.same_selection(&call))
            {
                return Err(refuse(
                    "redirection differs from this body's canonical native call selection",
                ));
            }
            facts
                .availability
                .checked(self.tcx, self.def_id, self.body_def)
                .map_err(|_| {
                    refuse("redirection lacks the original checked argument availability")
                })?;
            // Keep the original executable declaration's access, native type
            // arguments, WF/bounds and selected implementation dependencies.
            // The specification target receives its own ordinary checks below.
            self.check_function_access(def_id, span);
            let original_args = self.at_args(generic_args);
            super::autospec::check_call_arguments(
                self.cx,
                def_id,
                original_args,
                self.body_def,
                span,
            )
            .map_err(FnProblem::Refused)?;
            let uses = super::cycles::bound_impls(
                self.tcx,
                def_id,
                original_args,
                self.tcx.trait_of_assoc(def_id),
                Some(self.def_id.to_def_id()),
            )
            .map_err(FnProblem::Refused)?;
            self.record_impl_uses(uses);
            if call.declaration.to_def_id() != def_id {
                // A const function's native erased callee and its checked
                // logical declaration must both retain ordinary access,
                // argument WF/bounds and implementation dependencies.
                let declaration = call.declaration.to_def_id();
                self.check_function_access(declaration, span);
                super::autospec::check_call_arguments(
                    self.cx,
                    declaration,
                    original_args,
                    self.body_def,
                    span,
                )
                .map_err(FnProblem::Refused)?;
                let uses = super::cycles::bound_impls(
                    self.tcx,
                    declaration,
                    original_args,
                    self.tcx.trait_of_assoc(declaration),
                    Some(self.def_id.to_def_id()),
                )
                .map_err(FnProblem::Refused)?;
                self.record_impl_uses(uses);
            }
            let current = self
                .cx
                .autospec
                .call(self.cx, self.body_def, self.typeck, e)
                .map_err(FnProblem::Refused)?;
            if !current
                .as_ref()
                .is_some_and(|actual| actual.same_selection(&call))
                || !self
                    .cx
                    .checked_modes
                    .borrow()
                    .get(&self.def_id)
                    .is_some_and(|actual| std::rc::Rc::ptr_eq(actual, &facts))
            {
                return Err(refuse(
                    "native validation revoked the original redirection or mode packet",
                ));
            }
            facts
                .availability
                .checked(self.tcx, self.def_id, self.body_def)
                .map_err(|_| {
                    refuse("native validation revoked the original argument availability")
                })?;
            (call.target.to_def_id(), call.args)
        } else {
            if self
                .checked_modes
                .as_ref()
                .is_some_and(|facts| facts.autospec_calls.contains_key(&e.hir_id))
            {
                return refuse(
                    "autospec-modes",
                    "a completed ghost redirection reached another native context",
                    span,
                );
            }
            match constant {
                Some(call)
                    if call.kind == FnKind::ConstFunction
                        && call.original == def_id
                        && call.arguments == generic_args =>
                {
                    (call.declaration.to_def_id(), call.arguments)
                }
                Some(_) => {
                    return refuse(
                        "constant-use",
                        "a const function call changed its native role or arguments",
                        span,
                    )
                }
                None => (def_id, generic_args),
            }
        };
        let selected = self
            .cx
            .derived_clones
            .call(self.cx, self.body_def, self.typeck, e)
            .map_err(FnProblem::Refused)?;
        let (def_id, generic_args) = if let Some(call) = selected {
            let refuse =
                |reason| FnProblem::Refused(Refusal::new("derived-clone-modes", reason, span));
            let facts = self
                .checked_modes
                .as_ref()
                .ok_or_else(|| refuse("the derived call lacks a completed original mode walk"))?;
            if call.original != def_id
                || call.original_args != generic_args
                || !self
                    .cx
                    .checked_modes
                    .borrow()
                    .get(&self.def_id)
                    .is_some_and(|canonical| std::rc::Rc::ptr_eq(canonical, facts))
                || !facts
                    .derived_clone_calls
                    .get(&e.hir_id)
                    .is_some_and(|observed| observed.same_selection(&call))
            {
                return Err(refuse(
                    "the derived call is not this body's canonical native selection",
                ));
            }
            facts
                .availability
                .checked(self.tcx, self.def_id, self.body_def)
                .map_err(|_| {
                    refuse("the derived call's original availability facts are unavailable")
                })?;
            self.check_function_access(def_id, span);
            (call.method.to_def_id(), call.args)
        } else {
            (def_id, generic_args)
        };
        if !self.cx.fns.contains_key(&def_id) {
            if let Some(problem) = super::autospec::ignored_external_call(
                self.cx,
                self.def_id,
                self.body_def,
                self.typeck,
                e,
                def_id,
            ) {
                return Err(FnProblem::Rejected(problem));
            }
            return refuse(
                "external-call",
                format!(
                    "`{}` is not a Verus function of this crate",
                    self.tcx.def_path_str(def_id)
                ),
                span,
            );
        }
        // Verus checks a call before its arguments.
        self.check_function_access(def_id, span);
        let target = self.call_target(def_id, generic_args, span)?;
        match target.mode {
            Mode::Spec => {
                if ctx == Ctx::Exec
                    && !self.mode_rejected
                    && !self.cx.legacy_functions.contains(&self.def_id)
                {
                    return refuse(
                        "spec-call-in-exec",
                        "a spec function called from exec code",
                        span,
                    );
                }
                let values = self.operands(args, ctx, out)?;
                let ty = self.expr_ty(e)?;
                Ok(Expr::new(
                    ty,
                    self.sp(span),
                    ExprKind::Call {
                        callee: target.id,
                        type_args: target.type_args,
                        args: values,
                    },
                ))
            }
            Mode::Exec | Mode::Proof => {
                if ctx == Ctx::Spec && !self.mode_rejected {
                    return refuse(
                        "call-in-spec",
                        "an exec or proof function called from spec code",
                        span,
                    );
                }
                let values = self.operands(args, ctx, out)?;
                let ty = self.expr_ty(e)?;
                let dest = if discard {
                    None
                } else {
                    // Preserve the exact Proof result of the native-owned
                    // all-Proof call fragment, including its implicit Unit.
                    // Other used Unit values still transport raw prophecy;
                    // their eventual source consumer performs Unit clearing.
                    let transport_mode = if ty == Ty::Unit
                        && !self.native_proof_unit_transport(def_id, &target, args.len(), span)
                    {
                        Mode::Spec
                    } else {
                        target.ret_mode.unwrap_or(ctx.local_mode())
                    };
                    let t = self.temp_with_mode(ty.clone(), transport_mode, span);
                    if self.locals[t.index()].mode == Mode::Spec {
                        // The call, rather than a source no-init declaration,
                        // initializes this generated result. Infer its effect
                        // once from the actual call's arguments.
                        self.locals[t.index()].prophecy = DeclProphecy::DelayedInfer;
                    }
                    out.push(Stmt::new(
                        self.sp(span),
                        StmtKind::Let {
                            local: t,
                            init: None,
                        },
                    ));
                    Some(t)
                };
                let site = self.site();
                out.push(Stmt::new(
                    self.sp(span),
                    StmtKind::Call {
                        callee: target.id,
                        type_args: target.type_args,
                        args: values,
                        dest: dest.map(Place::local),
                        site,
                    },
                ));
                Ok(match dest {
                    Some(t) => self.read_local(t, span),
                    None if ty == Ty::Unit => self.unit(span),
                    // A discarded value: nothing reads it.
                    None => self.unit(span),
                })
            }
        }
    }

    /// Normalize actual native arguments before any codegen selection key.
    /// The exact caller environment is retained; an unavailable key refuses
    /// this whole read instead of selecting the generic declaration fallback.
    fn selection_args(
        &self,
        args: ty::GenericArgs<'tcx>,
        env: ty::TypingEnv<'tcx>,
        span: Span,
    ) -> R<ty::GenericArgs<'tcx>> {
        let tcx = self.tcx;
        let erased = tcx.erase_and_anonymize_regions(args);
        if erased.has_escaping_bound_vars() {
            return refuse(
                "trait-normalization",
                "trait selection arguments with an escaping type or const binder",
                span,
            );
        }
        let normalized = tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new(erased))
            .map_err(|problem| {
                FnProblem::Refused(Refusal::new(
                    "trait-normalization",
                    format!("cannot normalize native trait selection arguments: {problem:?}"),
                    span,
                ))
            })?;
        if normalized.has_escaping_bound_vars()
            || normalized.has_opaque_types()
            || normalized.has_infer()
            || normalized.has_placeholders()
            || normalized.references_error()
        {
            return refuse(
                "trait-normalization",
                "native trait selection arguments remain unsupported after normalization",
                span,
            );
        }
        Ok(normalized)
    }

    /// The method a call of the trait method `def_id` at `args` runs, as
    /// Verus resolves it (`rust_verify/src/resolve_traits.rs`,
    /// `resolve_trait_item`): the implementation rustc selects for the
    /// trait reference (in `env`), and in it the method implementing
    /// `def_id` (at the implementation's arguments followed by the method's
    /// own), or the trait's default method when the implementation does not
    /// override it (at `args`). `None` when no implementation is selected
    /// (a type parameter's bound, a builtin).
    fn resolve_trait_call(
        &self,
        def_id: DefId,
        args: ty::GenericArgs<'tcx>,
        env: ty::TypingEnv<'tcx>,
        span: Span,
    ) -> R<Option<(DefId, ty::GenericArgs<'tcx>)>> {
        let tcx = self.tcx;
        let Some(trait_id) = tcx.trait_of_assoc(def_id) else {
            return Ok(None);
        };
        let args = self.selection_args(args, env, span)?;
        let trait_ref = ty::TraitRef::new(
            tcx,
            trait_id,
            args.iter().take(tcx.generics_of(trait_id).count()),
        );
        let Ok(rustc_middle::traits::ImplSource::UserDefined(data)) =
            tcx.codegen_select_candidate(env.as_query_input(trait_ref))
        else {
            return Ok(None);
        };
        let implementing = tcx
            .associated_items(data.impl_def_id)
            .in_definition_order()
            .find(|item| item.trait_item_def_id() == Some(def_id))
            .map(|item| item.def_id);
        match implementing {
            Some(item) => Ok(Some((item, args.rebase_onto(tcx, trait_id, data.args)))),
            None => Ok(Some((def_id, args))),
        }
    }

    /// The implementation rustc selects for the trait of the trait method
    /// `def_id` at the concrete type arguments `args`.
    fn selected_impl(
        &self,
        def_id: DefId,
        args: ty::GenericArgs<'tcx>,
        span: Span,
    ) -> R<Option<DefId>> {
        let tcx = self.tcx;
        let Some(trait_id) = tcx.trait_of_assoc(def_id) else {
            return Ok(None);
        };
        let env = ty::TypingEnv::fully_monomorphized();
        let args = self.selection_args(args, env, span)?;
        let trait_ref = ty::TraitRef::new(
            tcx,
            trait_id,
            args.iter().take(tcx.generics_of(trait_id).count()),
        );
        match tcx.codegen_select_candidate(env.as_query_input(trait_ref)) {
            Ok(rustc_middle::traits::ImplSource::UserDefined(data)) => Ok(Some(data.impl_def_id)),
            _ => Ok(None),
        }
    }

    /// The shared declaration mode of a resolved call's result.
    fn call_result_mode(&self, def_id: DefId, span: Span) -> Option<Mode> {
        super::modes::call_return_mode(self.cx, def_id, span)
    }

    /// Transport mode only: this does not establish native ownership or prove
    /// a callee. Its original body and ordinary borrow/erase checks still run.
    fn native_proof_unit_transport(
        &self,
        callee: DefId,
        target: &Target,
        arity: usize,
        span: Span,
    ) -> bool {
        if target.mode != Mode::Proof
            || target.ret_mode != Some(Mode::Proof)
            || self.tcx.def_kind(callee) != DefKind::Fn
            || !self.cx.native_ownership.borrow().contains_key(&self.def_id)
        {
            return false;
        }
        let super::modes::SignatureModeResult::Known(signature) =
            super::modes::signature_modes(self.cx, callee, span)
        else {
            return false;
        };
        signature.def_id == callee
            && callee.as_local() == Some(signature.body_owner)
            && signature.mode == Mode::Proof
            && signature.ret.mode == Mode::Proof
            && !signature.prophetic
            && signature.params.len() == arity
            && signature.params.iter().all(|parameter| {
                parameter.declared.mode == Mode::Proof && !parameter.mutable_reference
            })
    }

    fn enum_diagnostic_call(&self, def_id: DefId, span: Span) -> Option<FnProblem> {
        if !self.cx.enum_diagnostics.contains(&def_id) {
            return None;
        }
        let mut error = UserError::new(
            Phase::RustToVir,
            span,
            "this field is present in multiple variants, cannot use -> syntax",
        );
        error.help = Some("use `matches` instead".into());
        Some(FnProblem::Rejected(error))
    }

    /// The function a call of `def_id` at `generic_args` runs, and its type
    /// arguments.
    ///
    /// * At concrete types (no type parameter in the arguments) a trait
    ///   method is resolved to its implementation, as rustc resolves it; a
    ///   generic function, or a default method an implementation does not
    ///   override, is called as an instance at those types. Verus checks such
    ///   a call against the trait declaration's `requires` and assumes the
    ///   resolved method's `ensures` (`vir/src/sst_to_air.rs`, `StmX::Call`),
    ///   which are the implementation's: its inherited clauses and its own.
    /// * In a generic body type arguments retain their complete represented
    ///   structure and the function's in-scope parameters; a trait method is
    ///   then its declaration, whose clauses hold for every implementation.
    fn call_target(
        &mut self,
        def_id: DefId,
        generic_args: ty::GenericArgs<'tcx>,
        span: Span,
    ) -> R<Target> {
        if let Some(problem) = self.enum_diagnostic_call(def_id, span) {
            return Err(problem);
        }
        let tcx = self.tcx;
        let args = self.at_args(generic_args);
        let info = |id: DefId| self.cx.fns.get(&id).copied();
        let Some(own) = info(def_id) else {
            return refuse(
                "external-call",
                format!(
                    "`{}` is not a Verus function of this crate",
                    tcx.def_path_str(def_id)
                ),
                span,
            );
        };
        if args.iter().any(|arg| arg.as_const().is_some()) {
            return refuse("generics", "a call with const arguments", span);
        }
        // Verus translates every type argument of a call and collects the
        // implementations that meet the callee's bounds at them
        // (`fn_call_to_vir.rs`, `mk_typ_args` and `get_impl_paths`), in the
        // function as written.
        let env = self.body_def.to_def_id();
        let mut argument_problem = None;
        for arg in generic_args.iter() {
            if let Some(problem) = self
                .cx
                .verus_arg_problem(arg, env)
                .map_err(FnProblem::Refused)?
            {
                argument_problem = Some(problem);
                break;
            }
        }
        let problem = match argument_problem {
            Some(problem) => Some(problem),
            None => self
                .cx
                .verus_bounds_problem(def_id, generic_args, env)
                .map_err(FnProblem::Refused)?,
        };
        if let Some(problem) = problem {
            return refuse(
                super::TAG_VERUS_TYPE,
                format!("{problem} in a call, which Verus does not translate"),
                span,
            );
        }
        // Verus's well-formedness check runs over the type arguments of
        // every call in the function (`well_formed.rs`, `check_expr`).
        for ty in generic_args.types() {
            if let Some(problem) = self
                .cx
                .verus_wf_problem(ty, env)
                .map_err(FnProblem::Refused)?
            {
                return refuse(
                    super::TAG_VERUS_WF,
                    format!("{problem} in a call's type arguments"),
                    span,
                );
            }
        }
        if let Some((id, arity)) = self.cx.imported_function(def_id) {
            if id != own.id
                || own.mode != Mode::Spec
                || self.call_result_mode(def_id, span) != Some(Mode::Spec)
                || tcx.trait_of_assoc(def_id).is_some()
                || args.len() != arity
            {
                return refuse(
                    "import-binding",
                    "the imported call lacks its exact native signature or modes",
                    span,
                );
            }
            // Imported declarations are called directly at both concrete and
            // parametric types. No local DefId or synthetic Instance exists.
            let mut type_args = Vec::new();
            for argument in args.iter() {
                let value = match argument.kind() {
                    ty::GenericArgKind::Type(value) => self.vc_ty(value)?,
                    _ => None,
                };
                let Some(value) = value else {
                    return refuse(
                        "generics",
                        "an imported call has unsupported or incomplete type arguments",
                        span,
                    );
                };
                type_args.push(value);
            }
            return Ok(Target {
                id,
                mode: Mode::Spec,
                ret_mode: Some(Mode::Spec),
                type_args,
            });
        }
        let is_trait_method = tcx.trait_of_assoc(def_id).is_some();
        if args.types().next().is_none() && !is_trait_method {
            return Ok(Target {
                id: own.id,
                mode: own.mode,
                ret_mode: self.call_result_mode(def_id, span),
                type_args: Vec::new(),
            });
        }
        if !args.has_param() {
            let (resolved, resolved_args) = if is_trait_method {
                match self.resolve_trait_call(
                    def_id,
                    args,
                    ty::TypingEnv::fully_monomorphized(),
                    span,
                )? {
                    Some(resolved) => {
                        // A default method the implementation inherits runs
                        // as Verus's copy for the implementation, which
                        // Verus makes only for an implementation it reads
                        // (`vir/src/traits.rs`, `inherit_default_bodies`);
                        // Verus's well-formedness check rejects a call of a
                        // copy it lacks, after the errors of earlier phases.
                        if resolved.0 == def_id && self.verify_refusal.is_none() {
                            if let Some(imp) = self.selected_impl(def_id, args, span)? {
                                if !super::is_verus_trait_impl(self.cx, imp) {
                                    self.verify_refusal = Some(Refusal::new(
                                        "external-call",
                                        format!(
                                            "`{}` is inherited by `{}`, which Verus does not read",
                                            tcx.def_path_str(def_id),
                                            tcx.def_path_str(imp)
                                        ),
                                        span,
                                    ));
                                }
                            }
                        }
                        resolved
                    }
                    None => {
                        return refuse(
                            "trait-resolve",
                            format!(
                                "a call of `{}` that does not resolve",
                                tcx.def_path_str(def_id)
                            ),
                            span,
                        )
                    }
                }
            } else {
                (def_id, args)
            };
            // The implementations the callee's bounds need at these types
            // (for the cycle check, `cycles`), as Verus collects them
            // (`fn_call_to_vir.rs`, `get_impl_paths`): for an implementation's
            // method, its own and its implementation's bounds; otherwise the
            // callee's, a trait method's without its `Self` bound.
            let uses = if resolved == def_id {
                super::cycles::bound_impls(tcx, def_id, args, tcx.trait_of_assoc(def_id), None)
            } else {
                super::cycles::bound_impls(tcx, resolved, resolved_args, None, None)
            };
            let uses = uses.map_err(FnProblem::Refused)?;
            self.record_impl_uses(uses);
            let Some(resolved_info) = info(resolved) else {
                return refuse(
                    "external-call",
                    format!(
                        "`{}` is implemented by `{}`, which is not a Verus function of this crate",
                        tcx.def_path_str(def_id),
                        tcx.def_path_str(resolved)
                    ),
                    span,
                );
            };
            if resolved_args.types().next().is_none() {
                return Ok(Target {
                    id: resolved_info.id,
                    mode: resolved_info.mode,
                    ret_mode: self.call_result_mode(resolved, span),
                    type_args: Vec::new(),
                });
            }
            let Some(id) = self.cx.instance(resolved, resolved_args) else {
                return refuse(
                    "generics",
                    "an instance of a function the reader does not know",
                    span,
                );
            };
            return Ok(Target {
                id,
                mode: resolved_info.mode,
                ret_mode: self.call_result_mode(resolved, span),
                type_args: Vec::new(),
            });
        }
        // In generic code rustc may still resolve a trait method call to one
        // implementation (a method of a generic implementation, at the
        // caller's type parameters); otherwise the call dispatches through
        // the declaration.
        let (callee, callee_args) = if is_trait_method {
            let env = ty::TypingEnv::non_body_analysis(tcx, self.def_id.to_def_id());
            match self.resolve_trait_call(def_id, args, env, span)? {
                // An implementation's method at the caller's type
                // parameters.
                Some((resolved, resolved_args)) if resolved != def_id => (resolved, resolved_args),
                // A default method the implementation does not override,
                // at types built from type parameters: an instance with type
                // parameters, which is not read yet.
                Some((_, resolved_args)) if resolved_args != args => {
                    return refuse(
                        "generics",
                        "a default method inherited at types built from type parameters",
                        span,
                    )
                }
                _ => (def_id, args),
            }
        } else {
            (def_id, args)
        };
        let Some(callee_info) = info(callee) else {
            return refuse(
                "external-call",
                format!(
                    "`{}` is not a Verus function of this crate",
                    tcx.def_path_str(callee)
                ),
                span,
            );
        };
        let env = Some(self.def_id.to_def_id());
        let uses = if callee == def_id {
            super::cycles::bound_impls(tcx, def_id, args, tcx.trait_of_assoc(def_id), env)
        } else {
            super::cycles::bound_impls(tcx, callee, callee_args, None, env)
        };
        let uses = uses.map_err(FnProblem::Refused)?;
        self.record_impl_uses(uses);
        // Verus guards the definition of a trait implementation's spec
        // method by the method's trait bounds. The clauses an
        // implementation's method inherits from a trait method may use it
        // where those bounds do not hold (the trait method's own bounds are
        // not the implementation method's), and then the function may not
        // see the definition.
        if callee_info.mode == Mode::Spec && tcx.trait_impl_of_assoc(callee).is_some() {
            if let Some(order) = super::cycles::unmet_bound(
                tcx,
                callee,
                callee_args,
                env,
                self.cx.opts.no_external_by_default,
            ) {
                let mut hides = self.cx.bound_hides.borrow_mut();
                let entry = hides.entry(self.own_id).or_default();
                let merged = match (entry.get(&callee_info.id), order) {
                    (Some(DefOrder::Later), _) | (_, DefOrder::Later) => DefOrder::Later,
                    _ => DefOrder::Unknown,
                };
                entry.insert(callee_info.id, merged);
            }
        }
        let mut type_args = Vec::new();
        for t in callee_args.types() {
            // Reuse the same native type conversion as parameters, values and
            // imported calls. It preserves complete nominal/decorated types
            // and refuses unsupported types or parameters outside this body.
            // All original argument, well-formedness and trait-bound checks
            // above still apply before this representation is constructed.
            let Some(argument) = self.vc_ty(t)? else {
                return refuse(
                    "generics",
                    format!(
                        "a generic call has an unsupported or out-of-scope type argument `{t}`"
                    ),
                    span,
                );
            };
            type_args.push(argument);
        }
        Ok(Target {
            id: callee_info.id,
            mode: callee_info.mode,
            ret_mode: self.call_result_mode(callee, span),
            type_args,
        })
    }

    /// A call of a Verus marker.
    ///
    /// A Spec intrinsic snapshots its logical reference argument; rustc's
    /// exact implicit reborrow does not create executable borrowed storage.
    /// Explicit `&mut` expressions still take the normal, closed borrow path.
    fn mut_ref_intrinsic_arg(
        &mut self,
        arg: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if self.is_reborrow(arg) {
            let previous = self.adjusting;
            self.adjusting = Some(arg.hir_id);
            let value = self.expr(arg, ctx, out);
            self.adjusting = previous;
            value
        } else {
            self.expr_adjusted(arg, ctx, out)
        }
    }

    /// A call of a Verus marker.
    fn marker(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        item: VerusItem,
        def_id: DefId,
        args: &[&'tcx hir::Expr<'tcx>],
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = e.span;
        let name = || self.tcx.def_path_str(def_id);
        match (item, args) {
            (VerusItem::SeqLen, _) => self.owned_seq_len(e, def_id, args, ctx, out),
            (VerusItem::SeqIndex, _) => self.owned_seq_index(e, def_id, args, ctx, out),
            (VerusItem::MutRefCurrent | VerusItem::MutRefFuture, [arg]) => {
                if !self.cx.opts.new_mut_ref || ctx == Ctx::Exec {
                    return refuse(
                        "new-mut-ref",
                        "mutable-reference spec functions require ghost code under -V new-mut-ref",
                        span,
                    );
                }
                let reference = self.mut_ref_intrinsic_arg(arg, ctx, out)?;
                let Ty::MutRef(inner) = &reference.ty else {
                    return refuse(
                        "new-mut-ref",
                        "a reference projection requires an opaque mutable reference",
                        span,
                    );
                };
                let result = self.expr_ty(e)?;
                if inner.as_ref() != &result {
                    return refuse(
                        "new-mut-ref",
                        "a reference projection changed its native referent type",
                        span,
                    );
                }
                let kind = if item == VerusItem::MutRefCurrent {
                    ExprKind::MutRefCurrent(Box::new(reference))
                } else {
                    ExprKind::MutRefFuture(Box::new(reference))
                };
                Ok(Expr::new(result, self.sp(span), kind))
            }
            (VerusItem::HasResolved | VerusItem::HasResolvedUnsized, [arg]) => {
                if !self.cx.opts.new_mut_ref || ctx == Ctx::Exec {
                    return refuse(
                        "new-mut-ref",
                        "has_resolved requires ghost code under -V new-mut-ref",
                        span,
                    );
                }
                if self.expr_ty(e)? != Ty::Bool {
                    return refuse(
                        "new-mut-ref",
                        "has_resolved has a non-Boolean native result",
                        span,
                    );
                }
                let mut value = self.mut_ref_intrinsic_arg(arg, ctx, out)?;
                if item == VerusItem::HasResolvedUnsized {
                    let Ty::Ref {
                        mutable: false,
                        inner,
                    } = value.ty.clone()
                    else {
                        return refuse(
                            "new-mut-ref",
                            "has_resolved_unsized expects a shared reference",
                            span,
                        );
                    };
                    value =
                        match value.kind {
                            ExprKind::Borrow(inner) => *inner,
                            ExprKind::Read(mut place) => {
                                place.projections.push(Projection::Deref);
                                Expr::read(place, *inner, self.sp(arg.span))
                            }
                            _ => return refuse(
                                "new-mut-ref",
                                "has_resolved_unsized of an unrepresented shared-reference value",
                                span,
                            ),
                        };
                }
                Ok(Expr::new(
                    Ty::Bool,
                    self.sp(span),
                    ExprKind::HasResolved(Box::new(value)),
                ))
            }
            (VerusItem::Final, [_]) => refuse(
                "new-mut-ref",
                "`final_` must be directly dereferenced",
                span,
            ),
            (VerusItem::Old, [arg]) if self.cx.opts.new_mut_ref => {
                // Only the original parameter place, not a fresh reborrow,
                // is named by this entry-state operation.
                if !self.is_reborrow(arg) {
                    self.no_adjustments(arg)?;
                }
                let place = self.place_unadjusted(arg)?;
                if !place.projections.is_empty() || !self.params.contains(&place.local) {
                    return refuse("old", "old requires the original parameter value", span);
                }
                let result = self.expr_ty(e)?;
                if self.locals[place.local.index()].ty != result {
                    return refuse("old", "old changed its original parameter type", span);
                }
                Ok(Expr::new(result, self.sp(span), ExprKind::Old(place)))
            }
            (VerusItem::GetVariantField, [receiver, variant, field]) => {
                self.local_variant_field(e, def_id, receiver, variant, field, ctx, out)
            }
            (VerusItem::IsVariant, [receiver, variant]) => {
                self.local_variant_test(e, def_id, receiver, variant, ctx, out)
            }
            (VerusItem::ConstrainType, [_, _]) if self.mode_rejected => {
                // Outside ensures the pinned reader treats this as an ordinary
                // Spec call, so its two real arguments must still be read. The
                // HIR mode checker has already rejected this function; keep
                // argument adjustments, effects and earlier reader errors, as
                // call_fn does, without turning the typing aid into a clause
                // erasure or assigning it a usable Spec definition.
                self.operands(args, ctx, out)?;
                // reader::read_crate discards this function's entire body and
                // clauses after collecting its mode error. This typed value is
                // only for that rejected-body walk; clean calls still refuse.
                Ok(Expr::bool_lit(false, self.sp(span)))
            }
            (VerusItem::ArchWordBits, []) => Ok(Expr::new(
                self.expr_ty(e)?,
                self.sp(e.span),
                ExprKind::IntegerConstant(trust_vc_vcir::IntegerConstant::WordBits),
            )),
            (VerusItem::Assert, [arg]) => {
                let attrs = self.clause_attrs(arg.hir_id)?;
                let expr = self.logical_in_syntax(arg, ctx)?;
                let site = self.site();
                // Verus reports a failed assertion at the argument as
                // written (a block keeps its braces); the marker call's own
                // span is only the `assert` name.
                out.push(Stmt::new(
                    self.sp(arg.span),
                    StmtKind::Assert { expr, site, attrs },
                ));
                Ok(self.unit(span))
            }
            (VerusItem::AssertBy, [cond, proof]) => {
                self.assert_by(cond, proof, ctx, span, out)?;
                Ok(self.unit(span))
            }
            (VerusItem::AssertBitvectorBy, [block]) => {
                self.assert_bitvector_by(e, block, ctx, out)?;
                Ok(self.unit(span))
            }
            (VerusItem::Forall, [arg]) => self.quant_expr(e, QuantKind::Forall, arg, ctx),
            (VerusItem::Exists, [arg]) => self.quant_expr(e, QuantKind::Exists, arg, ctx),
            (VerusItem::Choose, [arg]) => self.choose_expr(e, arg, false, ctx),
            (VerusItem::ChooseTuple, [arg]) => self.choose_expr(e, arg, true, ctx),
            (VerusItem::WithTriggers, [groups, body]) => self.with_triggers(groups, body),
            (VerusItem::AssertForallBy, [arg]) => {
                self.assert_forall_by(e, arg, ctx, out)?;
                Ok(self.unit(span))
            }
            (VerusItem::Assume, [arg]) => {
                let attrs = self.clause_attrs(arg.hir_id)?;
                let expr = self.logical_in_syntax(arg, ctx)?;
                out.push(Stmt::new(self.sp(span), StmtKind::Assume { expr, attrs }));
                Ok(self.unit(span))
            }
            (VerusItem::Admit, []) => {
                let expr = Expr::bool_lit(false, self.sp(span));
                out.push(Stmt::new(
                    self.sp(span),
                    StmtKind::Assume {
                        expr,
                        attrs: ClauseAttrs::default(),
                    },
                ));
                Ok(self.unit(span))
            }
            (VerusItem::RevealHide, [target, fuel]) => {
                self.reveal_hide(e, target, fuel, out)?;
                Ok(self.unit(span))
            }
            (VerusItem::Imply, [lhs, rhs]) => {
                // a ==> b is !a || b.
                let lv = self.expr(lhs, ctx, out)?;
                let mut rhs_out = Vec::new();
                let rv = self.expr(rhs, ctx, &mut rhs_out)?;
                if rhs_out.is_empty() {
                    return Ok(Expr::binary(
                        BinOp::Implies,
                        lv,
                        rv,
                        Ty::Bool,
                        self.sp(span),
                    ));
                }
                let not_lv = lv.not(self.sp(span));
                self.short_circuit_with(false, not_lv, rv, rhs_out, span, ctx, out)
            }
            (VerusItem::SpecEq | VerusItem::Equal, [lhs, rhs]) => {
                if self.cx.mentions_source_opaque(self.expr_rty_adj(lhs))
                    || self.cx.mentions_source_opaque(self.expr_rty_adj(rhs))
                {
                    return refuse(
                        "source-opaque-representation",
                        "opaque source equality requires its own semantic consumer",
                        span,
                    );
                }
                self.spec_eq(e, lhs, rhs, ctx, out)
            }
            (VerusItem::SpecOrd(ord), [lhs, rhs]) => {
                let (lv, rv) = self.operand_pair(lhs, rhs, ctx, out)?;
                if lv.ty.int_range().is_none() || rv.ty.int_range().is_none() {
                    return refuse("arith-type", "a spec comparison of non-integers", span);
                }
                let op = match ord {
                    OrdOp::Lt => BinOp::Lt,
                    OrdOp::Le => BinOp::Le,
                    OrdOp::Gt => BinOp::Gt,
                    OrdOp::Ge => BinOp::Ge,
                };
                self.comparison(op, lv, rv, span)
            }
            (VerusItem::SpecArith(arith), [lhs, rhs]) => {
                let (lv, rv) = self.operand_pair(lhs, rhs, ctx, out)?;
                let ty = self.expr_ty(e)?;
                let op = match arith {
                    SpecArith::Add => BinOp::Add,
                    SpecArith::Sub => BinOp::Sub,
                    SpecArith::Mul => BinOp::Mul,
                    SpecArith::Div => BinOp::Div,
                    SpecArith::Mod => BinOp::Rem,
                };
                self.spec_arith(op, lv, rv, ty, span)
            }
            (VerusItem::SpecNeg, [arg]) => {
                let value = self.expr(arg, ctx, out)?;
                if value.ty.int_range().is_none() {
                    return refuse("arith-type", "spec negation of a non-integer", span);
                }
                Ok(Expr::new(
                    Ty::int(),
                    self.sp(span),
                    ExprKind::Unary {
                        op: UnOp::Neg,
                        arg: Box::new(self.to_int(value)),
                        check: None,
                    },
                ))
            }
            (VerusItem::SpecBitwise(bits), [lhs, rhs]) => {
                let (lv, rv) = self.operand_pair(lhs, rhs, ctx, out)?;
                let op = match bits {
                    SpecBitwise::And => BinOpKind::BitAnd,
                    SpecBitwise::Or => BinOpKind::BitOr,
                    SpecBitwise::Xor => BinOpKind::BitXor,
                    SpecBitwise::Shl => BinOpKind::Shl,
                    SpecBitwise::Shr => BinOpKind::Shr,
                };
                self.arith_or_bits(op, lv, rv, Ctx::Spec, false, span)
            }
            (VerusItem::BuiltinArith(arith), [lhs, rhs]) => {
                let (lv, rv) = self.operand_pair(lhs, rhs, ctx, out)?;
                let ty = self.expr_ty(e)?;
                let op = match arith {
                    BuiltinArith::Add => BinOp::Add,
                    BuiltinArith::Sub => BinOp::Sub,
                    BuiltinArith::Mul => BinOp::Mul,
                };
                if lv.ty != ty || rv.ty != ty {
                    return refuse(
                        "arith-type",
                        "builtin arithmetic on operands of another type",
                        span,
                    );
                }
                match ty.int_range() {
                    Some(range) if range.is_bounded() => {
                        Ok(self.machine_arith(op, lv, rv, ty, ctx, span))
                    }
                    Some(_) => self.spec_arith(op, lv, rv, ty, span),
                    None => refuse("arith-type", "builtin arithmetic on a non-integer", span),
                }
            }
            (VerusItem::SpecLiteralInteger, [arg]) => self.spec_literal(e, arg, true),
            (VerusItem::SpecLiteralInt | VerusItem::SpecLiteralNat, [arg]) => {
                self.spec_literal(e, arg, false)
            }
            (VerusItem::SpecCastInteger, [arg]) => {
                let value = self.expr(arg, ctx, out)?;
                let to = self.expr_ty(e)?;
                self.scalar_cast(arg, value, to, ctx, span)
            }
            (
                VerusItem::Requires
                | VerusItem::Ensures
                | VerusItem::Recommends
                | VerusItem::OtherHeader,
                _,
            ) => refuse(
                "header-position",
                format!("`{}` after the function header", name()),
                span,
            ),
            (VerusItem::DummyCaptureNew | VerusItem::DummyCaptureConsume, _) => {
                refuse("closure", "closures are not read yet", span)
            }
            (VerusItem::Chained(ChainOp::Cmp), [chain]) => self.chained(chain, ctx, span),
            (VerusItem::IsSmallerThan, [lhs, rhs]) => {
                self.is_smaller_than(vec![*lhs], vec![*rhs], span)
            }
            (VerusItem::IsSmallerThanLexicographic, [lhs, rhs]) => {
                let (hir::ExprKind::Tup(smaller), hir::ExprKind::Tup(larger)) =
                    (lhs.kind, rhs.kind)
                else {
                    return refuse(
                        "verus-item",
                        "is_smaller_than_lexicographic of arguments that are not tuples",
                        span,
                    );
                };
                self.is_smaller_than(smaller.iter().collect(), larger.iter().collect(), span)
            }
            _ => refuse("verus-item", format!("`{}`", name()), span),
        }
    }

    /// The first read of a `&mut` parameter in `e` that is not through
    /// `old`: its name and span.
    fn mut_ref_read(&self, e: &Expr) -> Option<(String, Span)> {
        let mut found = None;
        let mut visit = |e: &Expr| {
            if found.is_some() {
                return;
            }
            if let ExprKind::Read(place) = &e.kind {
                let local = self.locals.get(place.local.index());
                let is_mut_ref_param = self.params.contains(&place.local)
                    && local.is_some_and(|l| matches!(l.ty, Ty::Ref { mutable: true, .. }));
                if is_mut_ref_param {
                    let name = local.map_or_else(String::new, |l| l.name.clone());
                    let at = self.cx.span_of(e.span).unwrap_or(rustc_span::DUMMY_SP);
                    found = Some((name, at));
                }
            }
        };
        walk_expr(e, &mut visit);
        found
    }

    /// `assert(p) by { proof }` (`ast_to_sst.rs`, `ExprX::AssertBy`): the
    /// proof and the check of `p` in a dead end, whose facts do not reach
    /// what follows, then `p` assumed. The dead end is a branch on an
    /// arbitrary condition that ends unreachable.
    fn assert_by(
        &mut self,
        cond: &'tcx hir::Expr<'tcx>,
        proof: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        span: Span,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        if ctx == Ctx::Exec
            && !self.mode_rejected
            && !self.cx.legacy_functions.contains(&self.def_id)
        {
            return refuse("assert-by", "assert .. by in exec code", span);
        }
        let attrs = self.clause_attrs(cond.hir_id)?;
        let expr = self.spec(cond)?;
        let hir::ExprKind::Block(block, None) = proof.kind else {
            return refuse(
                "assert-by",
                "an assert .. by whose proof is not a block",
                proof.span,
            );
        };
        let mut inner = Vec::new();
        self.block_stmts(block, Ctx::Proof, &mut inner)?;
        let site = self.site();
        inner.push(Stmt::new(
            self.sp(cond.span),
            StmtKind::Assert {
                expr: expr.clone(),
                site,
                attrs,
            },
        ));
        inner.push(Stmt::new(self.sp(span), StmtKind::Unreachable));
        let choice = self.temp(Ty::Bool, Ctx::Proof, span);
        let at = self.sp(span);
        out.push(Stmt::new(
            at,
            StmtKind::Let {
                local: choice,
                init: None,
            },
        ));
        out.push(Stmt::new(
            at,
            StmtKind::If {
                cond: self.read_local(choice, span),
                then_block: Block::new(inner),
                else_block: Block::default(),
            },
        ));
        out.push(Stmt::new(
            at,
            StmtKind::Assume {
                expr,
                attrs: ClauseAttrs::default(),
            },
        ));
        Ok(())
    }

    /// A `proof { .. }` block of spec code (`ExprX::ProofInSpec`): proof
    /// statements, only in the body of a spec function with a measure
    /// (`well_formed.rs`, `check_expr`). Elsewhere it is Verus's error and
    /// is dropped, as it is in a function the mode checker rejected.
    fn proof_in_spec_expr(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<Expr> {
        let span = e.span;
        let allowed =
            self.mode == Mode::Spec && self.area == Area::Body && !self.decreases.is_empty();
        if !allowed {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                span,
                messages::termination::PROOF_IN_SPEC_UNSUPPORTED,
            ));
            return Ok(self.unit(span));
        }
        if self.mode_rejected {
            return Ok(self.unit(span));
        }
        let hir::ExprKind::Block(block, None) = e.kind else {
            return refuse("expr", "a proof block that is not a block", span);
        };
        let mut out = Vec::new();
        for stmt in block.stmts {
            self.stmt(stmt, Ctx::Proof, &mut out)?;
        }
        let kind = if let Some(tail) = block.expr {
            let value = self.expr(tail, Ctx::Proof, &mut out)?;
            ExprKind::ProofInSpecTail {
                block: Block::new(out),
                tail: Box::new(value),
            }
        } else {
            ExprKind::ProofInSpec(Block::new(out))
        };
        Ok(Expr::new(Ty::Unit, self.sp(span), kind))
    }

    /// A chained comparison (`fn_call_to_vir.rs`, `ChainedItem`; expanded
    /// by `ast_simplify.rs`): each pair of neighbours compared, as
    /// integers, all of them holding.
    fn chained(&mut self, chain: &'tcx hir::Expr<'tcx>, ctx: Ctx, span: Span) -> R<Expr> {
        if ctx != Ctx::Spec && !self.mode_rejected {
            return refuse(
                "chained-comparison",
                "a chained comparison in exec code",
                span,
            );
        }
        let mut operands = Vec::new();
        let mut ops = Vec::new();
        let mut current = chain;
        loop {
            let hir::ExprKind::Call(func, args) = current.kind else {
                return refuse(
                    "chained-comparison",
                    "a chain of another shape",
                    current.span,
                );
            };
            match (self.callee_item(func).map(|(item, _)| item), args) {
                (Some(VerusItem::Chained(ChainOp::Value)), [first]) => {
                    operands.push(first);
                    break;
                }
                (Some(VerusItem::Chained(op)), [left, right]) if op != ChainOp::Cmp => {
                    operands.push(right);
                    ops.push(op);
                    current = left;
                }
                _ => {
                    return refuse(
                        "chained-comparison",
                        "a chain of another shape",
                        current.span,
                    )
                }
            }
        }
        operands.reverse();
        ops.reverse();
        let mut values = Vec::new();
        for operand in operands {
            let value = self.spec(operand)?;
            if value.ty.int_range().is_none() {
                return refuse(
                    "chained-comparison",
                    "a chained comparison of values that are not integers",
                    operand.span,
                );
            }
            values.push(self.to_int(value));
        }
        let at = self.sp(span);
        let mut out: Option<Expr> = None;
        for (op, pair) in ops.iter().zip(values.windows(2)) {
            let op = match op {
                ChainOp::Le => BinOp::Le,
                ChainOp::Lt => BinOp::Lt,
                ChainOp::Ge => BinOp::Ge,
                ChainOp::Gt => BinOp::Gt,
                ChainOp::Eq => BinOp::Eq,
                ChainOp::Value | ChainOp::Cmp => {
                    return refuse("chained-comparison", "a chain of another shape", span)
                }
            };
            let cmp = Expr::binary(op, pair[0].clone(), pair[1].clone(), Ty::Bool, at);
            out = Some(match out {
                None => cmp,
                Some(prev) => Expr::binary(BinOp::And, prev, cmp, Ty::Bool, at),
            });
        }
        out.map_or_else(
            || refuse("chained-comparison", "a chain without a comparison", span),
            Ok,
        )
    }

    /// `smaller` is below `larger` lexicographically (`fn_call_to_vir.rs`,
    /// `mk_is_smaller_than`): for integers, the first component that
    /// differs is at least 0 and below the other's; where the shared
    /// components are equal, `smaller` must have more of them. Heights of
    /// other values are not read yet.
    fn is_smaller_than(
        &mut self,
        smaller: Vec<&'tcx hir::Expr<'tcx>>,
        larger: Vec<&'tcx hir::Expr<'tcx>>,
        span: Span,
    ) -> R<Expr> {
        let at = self.sp(span);
        let mut pairs = Vec::new();
        for (a, b) in smaller.iter().zip(&larger) {
            let a = self.spec(a)?;
            let b = self.spec(b)?;
            if a.ty.int_range().is_none() || b.ty.int_range().is_none() {
                return refuse(
                    "height",
                    "the height of a value that is not an integer",
                    span,
                );
            }
            pairs.push((self.to_int(a), self.to_int(b)));
        }
        let lt = |a: &Expr, b: &Expr| {
            let zero = Expr::int_lit(0, Ty::int(), at);
            let lower = Expr::binary(BinOp::Le, zero, a.clone(), Ty::Bool, at);
            let below = Expr::binary(BinOp::Lt, a.clone(), b.clone(), Ty::Bool, at);
            Expr::binary(BinOp::And, lower, below, Ty::Bool, at)
        };
        let eq = |a: &Expr, b: &Expr| Expr::binary(BinOp::Eq, a.clone(), b.clone(), Ty::Bool, at);
        let longer = larger.len() < smaller.len();
        let mut out = Expr::bool_lit(longer, at);
        for (i, (a, b)) in pairs.iter().rev().enumerate() {
            out = if i == 0 {
                if longer {
                    Expr::binary(BinOp::Or, lt(a, b), eq(a, b), Ty::Bool, at)
                } else {
                    lt(a, b)
                }
            } else {
                let tail = Expr::binary(BinOp::And, eq(a, b), out, Ty::Bool, at);
                Expr::binary(BinOp::Or, lt(a, b), tail, Ty::Bool, at)
            };
        }
        Ok(out)
    }

    /// [`Self::short_circuit`] for a right side that is already lowered.
    #[allow(clippy::too_many_arguments)]
    fn short_circuit_with(
        &mut self,
        is_and: bool,
        lv: Expr,
        rv: Expr,
        mut rhs_out: Vec<Stmt>,
        span: Span,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        if ctx == Ctx::Spec && !self.mode_rejected {
            return refuse("effect-in-spec", "spec code with an effect", span);
        }
        let t = self.temp(Ty::Bool, ctx, span);
        if self.locals[t.index()].mode == Mode::Spec {
            // Preserve this short-circuit expression's guard/arm effect
            // through the generated result's branch initialization.
            self.locals[t.index()].prophecy = DeclProphecy::DelayedInfer;
        }
        let sid = self.sp(span);
        out.push(Stmt::new(
            sid,
            StmtKind::Let {
                local: t,
                init: None,
            },
        ));
        rhs_out.push(Stmt::new(
            sid,
            StmtKind::Assign {
                place: Place::local(t),
                value: rv,
            },
        ));
        let constant = vec![Stmt::new(
            sid,
            StmtKind::Assign {
                place: Place::local(t),
                value: Expr::bool_lit(!is_and, sid),
            },
        )];
        let (then_block, else_block) = if is_and {
            (rhs_out, constant)
        } else {
            (constant, rhs_out)
        };
        out.push(Stmt::new(
            sid,
            StmtKind::If {
                cond: lv,
                then_block: Block::new(then_block),
                else_block: Block::new(else_block),
            },
        ));
        Ok(self.read_local(t, span))
    }

    /// Spec arithmetic with result type `ty`: exact on `int`/`nat`; on a
    /// machine type (Euclidean `/` and `%` of machine operands) computed on
    /// `int` and taken back into the type.
    fn spec_arith(&self, op: BinOp, lv: Expr, rv: Expr, ty: Ty, span: Span) -> R<Expr> {
        let (Some(_), Some(_), Some(range)) =
            (lv.ty.int_range(), rv.ty.int_range(), ty.int_range())
        else {
            return refuse("arith-type", "spec arithmetic on non-integers", span);
        };
        let sid = self.sp(span);
        if range == trust_vc_vcir::IntRange::Nat {
            let nat = Ty::nat();
            let as_nat = |e: Expr| -> R<Expr> {
                match e.ty.int_range() {
                    Some(r) if trust_vc_vcir::IntRange::Nat.contains(r, 64) => Ok(if e.ty == nat {
                        e
                    } else {
                        let s = e.span;
                        e.cast(CastKind::Exact, Ty::nat(), s)
                    }),
                    _ => refuse(
                        "arith-type",
                        "nat arithmetic on a possibly negative operand",
                        span,
                    ),
                }
            };
            let (lv, rv) = (as_nat(lv)?, as_nat(rv)?);
            if op == BinOp::Sub {
                return refuse("arith-type", "nat subtraction", span);
            }
            return Ok(Expr::binary(op, lv, rv, ty, sid));
        }
        let exact = Expr::binary(op, self.to_int(lv), self.to_int(rv), Ty::int(), sid);
        if range == trust_vc_vcir::IntRange::Int {
            Ok(exact)
        } else {
            Ok(exact.cast(CastKind::As, ty, sid))
        }
    }

    /// `spec_literal_*("digits")`.
    /// `spec_literal_integer("..")` (whose value must fit its type, as
    /// `check_range` asks), `spec_literal_int` or `spec_literal_nat`.
    fn spec_literal(&self, e: &hir::Expr<'_>, arg: &hir::Expr<'_>, check_range: bool) -> R<Expr> {
        let span = e.span;
        let hir::ExprKind::Lit(lit) = arg.kind else {
            return refuse(
                "literal",
                "a spec literal whose argument is not a string",
                span,
            );
        };
        let AstLitKind::Str(symbol, _) = lit.node else {
            return refuse(
                "literal",
                "a spec literal whose argument is not a string",
                span,
            );
        };
        let digits: String = symbol.as_str().chars().filter(|c| *c != '_').collect();
        let Ok(magnitude) = digits.parse::<u128>() else {
            return refuse(
                "literal",
                format!("spec literal `{}`", symbol.as_str()),
                span,
            );
        };
        let ty = self.expr_ty(e)?;
        if ty.int_range().is_none() {
            return refuse("literal", "a spec literal of a non-integer type", span);
        }
        if check_range {
            check_lit_int(span, false, magnitude, &ty, self.cx.architecture)?;
        }
        Ok(Expr::new(
            ty,
            self.sp(span),
            ExprKind::Lit(Lit::Int(IntLit {
                negative: false,
                magnitude,
            })),
        ))
    }

    /// Spec `==`: Verus's type rule first, then the comparison.
    fn spec_eq(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Expr> {
        let span = e.span;
        let t1 = self.expr_rty_adj(lhs);
        let t2 = self.expr_rty_adj(rhs);
        match (self.cx.v_typ(t1), self.cx.v_typ(t2)) {
            (Some(v1), Some(v2)) => {
                if !spec_eq_compatible(&v1, &v2) {
                    let mut error = UserError::new(Phase::RustToVir, span, messages::SPEC_EQ_TYPES);
                    error.labels.push((
                        lhs.span,
                        messages::spec_eq_type_label(&v1.undecorate().to_diagnostic_string()),
                    ));
                    error.labels.push((
                        rhs.span,
                        messages::spec_eq_type_label(&v2.undecorate().to_diagnostic_string()),
                    ));
                    error.help = Some(messages::SPEC_EQ_TYPES_HELP.to_string());
                    return Err(FnProblem::Rejected(error));
                }
            }
            // Types the reader cannot name are only accepted when rustc sees
            // them as the same type.
            _ if t1 == t2 => {}
            _ => {
                return refuse(
                    "spec-eq-type",
                    format!("spec `==` between `{t1}` and `{t2}`"),
                    span,
                )
            }
        }
        if !self.cx.opts.new_mut_ref {
            if let ty::Ref(_, _, mutability) = t1.kind() {
                if mutability.is_mut() {
                    return Err(FnProblem::Rejected(UserError::new(
                        Phase::RustToVir,
                        lhs.span,
                        messages::SPEC_EQ_MUT_REF,
                    )));
                }
            }
        }
        let (mut lv, mut rv) = self.operand_pair(lhs, rhs, ctx, out)?;
        if lv.ty != rv.ty {
            lv = self.primitive_spec_eq_value(self.expr_rty(lhs), t1, lv, lhs.span)?;
            rv = self.primitive_spec_eq_value(self.expr_rty(rhs), t2, rv, rhs.span)?;
        }
        if lv.ty.int_range().is_none() && lv.ty != rv.ty {
            return refuse(
                "spec-eq-type",
                "spec `==` between differently decorated types",
                span,
            );
        }
        self.comparison(BinOp::Eq, lv, rv, span)
    }

    /// `reveal_hide_({ fn __VERUS_REVEAL_INTERNAL__() { reveal_hide_internal_path_(f) } .. }, n)`:
    /// fuel 0 hides `f`, fuel 1 reveals it, a larger fuel reveals it with
    /// that fuel. `broadcast use f;` in a function body expands to the same
    /// call with fuel 1, its block's last expression marked
    /// `broadcast_use_reveal`; it is not a reveal of `f`.
    fn reveal_hide(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        target: &'tcx hir::Expr<'tcx>,
        fuel: &'tcx hir::Expr<'tcx>,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        let span = e.span;
        let hir::ExprKind::Lit(fuel_lit) = fuel.kind else {
            return refuse("header-shape", "reveal with a non-literal fuel", span);
        };
        let AstLitKind::Int(fuel_value, suffix) = fuel_lit.node else {
            return refuse("header-shape", "reveal with a non-integer fuel", span);
        };
        let Some(callee) = self.reveal_target(target) else {
            return refuse(
                "header-shape",
                "a reveal whose target the reader cannot find",
                span,
            );
        };
        // Verus resolves the target first, then takes only an unsuffixed
        // literal that fits in `u32`: `0u32` is its error, not a `hide`.
        let fuel = match (suffix, u32::try_from(fuel_value.get())) {
            (LitIntType::Unsuffixed, Ok(fuel)) => fuel,
            _ => {
                return Err(FnProblem::Rejected(UserError::new(
                    Phase::RustToVir,
                    span,
                    messages::FUEL_NOT_U32,
                )))
            }
        };
        let Some(info) = self.cx.fns.get(&callee).copied() else {
            return refuse(
                "external-call",
                format!(
                    "reveal of `{}`, which is not a function of this crate",
                    self.tcx.def_path_str(callee)
                ),
                span,
            );
        };
        let Some(local) = callee.as_local() else {
            return refuse(
                "external-call",
                "reveal of a function of another crate",
                span,
            );
        };
        let target_attrs =
            attrs::item_attrs(self.tcx.hir_attrs(self.tcx.local_def_id_to_hir_id(local)));
        let target_module = self.tcx.parent_module_from_def_id(local).to_mod_id();
        if self.is_broadcast_use(target) {
            // Verus (`well_formed.rs`, `ExprX::Fuel`) accepts a `broadcast
            // use` only of a broadcast proof function or a broadcast group.
            // Both carry an attribute the reader does not read, so their
            // items are refused; any other target is Verus's error.
            if fuel != 1 {
                return refuse(
                    "header-shape",
                    "a `broadcast use` with a fuel other than 1",
                    span,
                );
            }
            if !target_attrs.unsupported.is_empty() {
                return refuse(
                    "broadcast-use",
                    "`broadcast use` of an item the reader does not read",
                    span,
                );
            }
            if target_attrs.broadcast_forall && info.mode == Mode::Proof {
                if self.tcx.generics_of(callee).count() != 0
                    || self.tcx.def_kind(self.tcx.parent(callee)) != DefKind::Mod
                {
                    return refuse(
                        "broadcast-use",
                        "a broadcast target outside the local monomorphic free-function fragment",
                        span,
                    );
                }
                out.push(Stmt::new(
                    self.sp(span),
                    StmtKind::BroadcastUse { callee: info.id },
                ));
                return Ok(());
            }
            self.errors.push(UserError::new(
                Phase::WellFormed,
                span,
                messages::wf::BROADCAST_USE_NOT_BROADCAST,
            ));
            return Ok(());
        }
        if fuel == 0 {
            if !self.header_hides.contains(&e.hir_id) {
                if self.body_tail == Some(e.hir_id) {
                    return refuse("header-position", "`hide` as the value of the body", span);
                }
                self.errors.push(UserError::new(
                    Phase::WellFormed,
                    span,
                    messages::wf::HIDE_NOT_AT_START,
                ));
                return Ok(());
            }
            // Verus turns `hide` into a header of the function, with none of
            // the checks of a reveal, and declares no fuel for a function
            // without a body, or for one of another module that this
            // module's queries do not use: hiding such a function makes
            // Verus fail with an internal error.
            if info.mode != Mode::Spec {
                return refuse("hide-target", "hide of a function that is not spec", span);
            }
            if target_attrs.external_body || target_attrs.uninterp {
                return refuse("hide-target", "hide of a function without a body", span);
            }
            if ty::Visibility::Restricted(target_module) != self.own_module() {
                return refuse("hide-target", "hide of a function of another module", span);
            }
        } else if info.mode != Mode::Spec {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                span,
                messages::wf::reveal_not_spec(info.mode.name()),
            ));
            return Ok(());
        } else if fuel > 1 && !self.has_decreases(local) {
            // `reveal_with_fuel` needs a `decreases` clause
            // (`well_formed.rs`, `ExprX::Fuel`).
            self.errors.push(UserError::new(
                Phase::WellFormed,
                span,
                messages::wf::REVEAL_WITH_FUEL_NO_DECREASES,
            ));
        } else {
            // The body is visible where the reveal is: an `open` body where
            // the function is, any other body in its module, an
            // `uninterp` function's nowhere.
            let body = if target_attrs.uninterp {
                None
            } else if target_attrs.open && !target_attrs.external_body {
                Some(self.tcx.visibility(callee))
            } else {
                Some(ty::Visibility::Restricted(target_module))
            };
            let here = self.own_module();
            if !body.is_some_and(|body| covers(self.tcx, body, here)) {
                self.errors.push(UserError::new(
                    Phase::WellFormed,
                    span,
                    messages::wf::reveal_closed(&self.cx.friendly_fn_path(callee)),
                ));
            } else if target_attrs.external_body && self.verify_refusal.is_none() {
                // Verus declares no fuel for a function without a body, and
                // revealing one fails with an internal error once it
                // verifies: an error of an earlier phase comes first.
                self.verify_refusal = Some(Refusal::new(
                    "reveal-target",
                    "reveal of a function without a body",
                    span,
                ));
            }
        }
        let kind = match fuel {
            0 => StmtKind::Hide { callee: info.id },
            1 => StmtKind::Reveal {
                callee: info.id,
                fuel: None,
            },
            n => StmtKind::Reveal {
                callee: info.id,
                fuel: Some(n),
            },
        };
        out.push(Stmt::new(self.sp(span), kind));
        Ok(())
    }

    /// Does the body of `function` have a `decreases` header?
    fn has_decreases(&self, function: LocalDefId) -> bool {
        let tcx = self.tcx;
        let Some(body) = tcx.hir_maybe_body_owned_by(function) else {
            return false;
        };
        let hir::ExprKind::Block(block, None) = body.value.kind else {
            return false;
        };
        let typeck = tcx.typeck(function);
        block.stmts.iter().any(|stmt| {
            let hir::StmtKind::Semi(e) = stmt.kind else {
                return false;
            };
            let hir::ExprKind::Call(func, _) = e.kind else {
                return false;
            };
            let hir::ExprKind::Path(qpath) = &func.kind else {
                return false;
            };
            match typeck.qpath_res(qpath, func.hir_id) {
                Res::Def(_, def_id) => {
                    self.cx.verus_item(def_id) == Some(VerusItem::OtherHeader)
                        && tcx.item_name(def_id).as_str() == "decreases"
                }
                _ => false,
            }
        })
    }

    /// Whether a reveal's target block ends in an expression marked
    /// `broadcast_use_reveal`, which makes it a `broadcast use`
    /// (`rust_verify/src/reveal_hide.rs`).
    fn is_broadcast_use(&self, target: &hir::Expr<'_>) -> bool {
        let hir::ExprKind::Block(block, None) = target.kind else {
            return false;
        };
        block.expr.is_some_and(|tail| {
            attrs::verus_attrs(self.tcx.hir_attrs(tail.hir_id))
                .iter()
                .any(|(attr, _)| *attr == VerusAttr::BroadcastUseReveal)
        })
    }

    /// The function named inside a reveal's helper function.
    fn reveal_target(&self, target: &hir::Expr<'_>) -> Option<DefId> {
        let hir::ExprKind::Block(block, None) = target.kind else {
            return None;
        };
        let helper = block.stmts.iter().find_map(|s| match s.kind {
            hir::StmtKind::Item(item) => Some(item.owner_id.def_id),
            _ => None,
        })?;
        let body = self.tcx.hir_body_owned_by(helper);
        let hir::ExprKind::Block(inner, None) = body.value.kind else {
            return None;
        };
        let call = inner.expr.or_else(|| {
            inner.stmts.iter().find_map(|s| match s.kind {
                hir::StmtKind::Semi(e) | hir::StmtKind::Expr(e) => Some(e),
                _ => None,
            })
        })?;
        let hir::ExprKind::Call(func, [path]) = call.kind else {
            return None;
        };
        // The helper is a separate body; its paths are resolved in HIR.
        let hir::ExprKind::Path(QPath::Resolved(None, func_path)) = func.kind else {
            return None;
        };
        let func_id = func_path.res.opt_def_id()?;
        if self.cx.verus_item(func_id) != Some(VerusItem::RevealHideInternalPath) {
            return None;
        }
        let hir::ExprKind::Path(QPath::Resolved(None, path)) = path.kind else {
            return None;
        };
        match path.res {
            Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => Some(def_id),
            _ => None,
        }
    }
}

/// Does `wide` reach everywhere `narrow` reaches? This is Verus's
/// `narrow.at_least_as_restrictive_as(wide)`.
fn covers(tcx: TyCtxt<'_>, wide: ty::Visibility<ModId>, narrow: ty::Visibility<ModId>) -> bool {
    match narrow {
        ty::Visibility::Public => wide.is_public(),
        ty::Visibility::Restricted(module) => wide.is_accessible_from(module, tcx),
    }
}

/// Does `e` contain an exec check site? A proof block's checks are its
/// own statements'.
fn has_checks(e: &Expr) -> bool {
    e.any(&|sub| {
        matches!(
            sub.kind,
            ExprKind::Unary { check: Some(_), .. } | ExprKind::Binary { check: Some(_), .. }
        )
    })
}

/// Call `f` on `e` and its subexpressions, outermost first.
fn walk_expr(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    e.for_each_child(&mut |child| walk_expr(child, f));
}

/// The header slot of a `decreases`-family header: `decreases_by` and
/// `recommends_by` share one (`headers.rs`, `HeaderExprX::DecreasesBy`).
fn termination_slot(name: &str) -> &'static str {
    match name {
        "decreases" => "decreases",
        "decreases_when" => "decreases_when",
        _ => "decreases_by",
    }
}

/// Verus's error for `&` or `|` (and `&=`, `|=`) on two bools, which it does
/// not support, at the left operand.
fn bool_bitwise_error(op: BinOpKind, lhs: Span) -> UserError {
    let feature = if op == BinOpKind::BitAnd {
        messages::BOOL_BITAND_FEATURE
    } else {
        messages::BOOL_BITOR_FEATURE
    };
    UserError::new(Phase::RustToVir, lhs, messages::unsupported(feature))
}

/// May `stmts` write a place whose root is `root`? An assignment or a call
/// result stored under `root` does; so may a call given a `&mut` argument,
/// which is counted whatever it borrows.
fn may_write_local(stmts: &[Stmt], root: LocalId) -> bool {
    stmts.iter().any(|stmt| match &stmt.kind {
        StmtKind::Assign { place, .. } | StmtKind::AssignSpec { place, .. } => place.local == root,
        StmtKind::BorrowMut { dest, place } => *dest == root || place.local == root,
        StmtKind::Call { args, dest, .. } => {
            dest.as_ref().is_some_and(|dest| dest.local == root)
                || args
                    .iter()
                    .any(|arg| matches!(arg.ty, Ty::Ref { mutable: true, .. } | Ty::MutRef(_)))
        }
        StmtKind::If {
            then_block,
            else_block,
            ..
        }
        | StmtKind::IfSpec {
            then_block,
            else_block,
            ..
        } => may_write_local(&then_block.stmts, root) || may_write_local(&else_block.stmts, root),
        StmtKind::Ghost(block) | StmtKind::Block(block) => may_write_local(&block.stmts, root),
        StmtKind::GhostTail { block, tail } => {
            may_write_local(&block.stmts, root) || expr_may_write_local(tail, root)
        }
        StmtKind::Loop(lp) => {
            lp.cond
                .as_ref()
                .is_some_and(|cond| may_write_local(&cond.block.stmts, root))
                || may_write_local(&lp.body.stmts, root)
        }
        StmtKind::Let { .. }
        | StmtKind::LetChecked { .. }
        | StmtKind::Assert { .. }
        | StmtKind::AssertBitVector { .. }
        | StmtKind::Assume { .. }
        | StmtKind::Return { .. }
        | StmtKind::BroadcastUse { .. }
        | StmtKind::Reveal { .. }
        | StmtKind::Hide { .. }
        | StmtKind::Break { .. }
        | StmtKind::Continue { .. }
        | StmtKind::Unreachable => false,
    })
}

fn expr_may_write_local(expr: &Expr, root: LocalId) -> bool {
    let mut writes = match &expr.kind {
        ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } => {
            may_write_local(&block.stmts, root)
        }
        _ => false,
    };
    expr.for_each_child(&mut |child| writes |= expr_may_write_local(child, root));
    writes
}

/// The binary operator of a compound assignment.
fn assign_op_kind(op: hir::AssignOpKind) -> BinOpKind {
    match op {
        hir::AssignOpKind::AddAssign => BinOpKind::Add,
        hir::AssignOpKind::SubAssign => BinOpKind::Sub,
        hir::AssignOpKind::MulAssign => BinOpKind::Mul,
        hir::AssignOpKind::DivAssign => BinOpKind::Div,
        hir::AssignOpKind::RemAssign => BinOpKind::Rem,
        hir::AssignOpKind::BitXorAssign => BinOpKind::BitXor,
        hir::AssignOpKind::BitAndAssign => BinOpKind::BitAnd,
        hir::AssignOpKind::BitOrAssign => BinOpKind::BitOr,
        hir::AssignOpKind::ShlAssign => BinOpKind::Shl,
        hir::AssignOpKind::ShrAssign => BinOpKind::Shr,
    }
}

/// A short name for an expression kind the reader refuses.
fn expr_kind_name(kind: &hir::ExprKind<'_>) -> &'static str {
    match kind {
        hir::ExprKind::ConstBlock(_) => "const blocks",
        hir::ExprKind::Array(_) => "arrays",
        hir::ExprKind::Use(..) => "`.use`",
        hir::ExprKind::Type(..) => "type ascription",
        hir::ExprKind::Loop(..) => "loops",
        hir::ExprKind::Match(..) => "match",
        hir::ExprKind::Block(_, Some(_)) => "labeled blocks",
        hir::ExprKind::Index(..) => "indexing",
        hir::ExprKind::AddrOf(..) => "borrows",
        hir::ExprKind::Break(..) => "break",
        hir::ExprKind::Continue(..) => "continue",
        hir::ExprKind::Ret(..) => "return in expression position",
        hir::ExprKind::Become(..) => "become",
        hir::ExprKind::InlineAsm(..) => "inline assembly",
        hir::ExprKind::OffsetOf(..) => "offset_of",
        hir::ExprKind::Repeat(..) => "array repeat",
        hir::ExprKind::Yield(..) => "yield",
        hir::ExprKind::UnsafeBinderCast(..) => "unsafe binder casts",
        hir::ExprKind::Err(_) => "an expression with errors",
        _ => "this expression kind",
    }
}

/// `{ break; }`: the `else` rustc builds for a `while`.
fn is_plain_break_block(e: &hir::Expr<'_>) -> bool {
    let hir::ExprKind::Block(block, None) = e.kind else {
        return false;
    };
    let ([stmt], None) = (block.stmts, block.expr) else {
        return false;
    };
    let (hir::StmtKind::Expr(inner) | hir::StmtKind::Semi(inner)) = stmt.kind else {
        return false;
    };
    matches!(
        inner.kind,
        hir::ExprKind::Break(hir::Destination { label: None, .. }, None)
    )
}
