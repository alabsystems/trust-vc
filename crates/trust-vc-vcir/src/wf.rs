//! Well-formedness: types, modes and the Verus errors this layer owns.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! [`check_crate`] reports two classes of problems:
//!
//! * [`WfClass::User`]: an error in the verified program that Verus reports
//!   as well. The message is Verus's text, so a producer can show it as is.
//! * [`WfClass::Malformed`]: the producer built something VcIR does not
//!   allow (a type mismatch, a dangling id, an exec check in spec code). This
//!   is a producer bug or an unsupported shape, never the user's fault; a
//!   producer reports it as a refusal.
//!
//! The VC generator only accepts a crate with no problems of either class.

use std::cell::{Cell, OnceCell};
use std::collections::{HashMap, HashSet};

use crate::expr::{BinOp, CastKind, Expr, ExprKind, Lit, Place, Projection, UnOp};
use crate::ids::{AdtId, FnId, LocalId, LoopId, ProjectionId, SiteId, SpanId};
use crate::item::{
    AdtDecl, AdtKind, Body, Clause, ConstMode, FnDecl, FnKind, FnRole, LocalKind, Mode,
    ProjectionDecl, VcCrate,
};
use crate::stmt::{Block, ClauseAttrs, InvariantKind, Loop, Stmt, StmtKind};
use crate::ty::{IntRange, Ty};

mod unwind;
mod value_modes;

/// Which side a problem is on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WfClass {
    /// An error in the verified program, reported with Verus's message.
    User,
    /// The producer built invalid VcIR.
    Malformed,
}

/// One problem found by [`check_crate`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WfError {
    /// User error or malformed IR.
    pub class: WfClass,
    /// The function the problem is in, if any.
    pub function: Option<FnId>,
    /// Where to report it.
    pub span: SpanId,
    /// What is wrong.
    pub message: String,
}

/// The exact mode distinction used by the Ghost-wrapper prophecy rule.
/// Exec and Proof both forbid a prophetic tail; Spec permits it. This quotient
/// preserves joins: the class of a join is Spec exactly when either arm is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GhostTailModeClass {
    /// A specification value.
    Spec,
    /// An executable or proof value.
    NonSpec,
}

impl From<Mode> for GhostTailModeClass {
    fn from(mode: Mode) -> Self {
        if mode == Mode::Spec {
            Self::Spec
        } else {
            Self::NonSpec
        }
    }
}

/// A raw Unit-tail mode class derived from the IR's actual value producers.
///
/// Rows are ordered by crate function order, then physical depth-first
/// evaluation order: a GhostTail's prefix and tail precede its own row.
/// They are diagnostics, not native source or ownership authority. `None`
/// means an absent, contradictory, or unsupported value origin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GhostTailModeObservation {
    /// The function containing this physical occurrence.
    pub function: FnId,
    /// The proof block's source position, never a mode permission.
    pub span: SpanId,
    /// Checked raw value mode class, before Unit consumption.
    pub class: Option<GhostTailModeClass>,
}

/// Derive raw proof-block tail modes even for prophecy-rejected crates.
/// Native producers compare every row with their same-context HIR mode facts;
/// a missing or unknown row never supplies a permissive Spec default.
#[must_use]
pub fn ghost_tail_modes(krate: &VcCrate) -> Vec<GhostTailModeObservation> {
    crate::prophecy::ghost_tail_modes(krate)
}

/// Inspect the existing prophecy effect pass for one actual function, before
/// public diagnostics suppress instance user errors already attributed to source.
/// The declaration, body, instance origin, and diagnostic function ID are retained.
///
/// This is a partial diagnostic view, not full well-formedness or verification:
/// it supplies no source, compiler, import, or ownership authority. An empty
/// result does not establish that types, modes, or instance origins are valid.
/// Returns `None` if the function ID is absent.
#[must_use]
pub fn function_prophecy_diagnostics(krate: &VcCrate, function: FnId) -> Option<Vec<WfError>> {
    let fns: HashMap<_, _> = krate.fns.iter().map(|decl| (decl.id, decl)).collect();
    let declaration = fns.get(&function).copied()?;
    Some(crate::prophecy::check_function(&fns, declaration))
}

/// Verus's message for a second `proof_note` or `custom_err` attribute.
pub const MSG_DUPLICATE_NOTE: &str = "at most one `proof_note` attribute is allowed";
/// Verus's message for an assignment in a spec function body.
pub const MSG_ASSIGN_IN_PURE: &str = "assignment is not allowed inside pure context";
/// Verus's message for a `mut` parameter of a spec function.
pub const MSG_MUT_SPEC_PARAM: &str = "mut argument not allowed for spec functions";
/// Verus's message for calling a proof function from exec code.
pub const MSG_CALL_PROOF_FROM_EXEC: &str = "cannot call function with mode proof";

/// Verus's message for assigning an immutable parameter.
#[must_use]
pub fn msg_not_mutable(name: &str) -> String {
    format!("variable `{name}` is not marked mutable")
}

/// Check a whole crate. An empty result means the crate is well formed.
#[must_use]
pub fn check_crate(krate: &VcCrate) -> Vec<WfError> {
    check_crate_impl(krate, false).errors
}

/// Findings from incomplete source construction. This is an error-reporting
/// view, not a well-formedness verdict or permission to generate any VC.
#[derive(Debug)]
pub struct DiagnosticWf {
    /// All ordinary type, mode, header and body errors found by the walk.
    pub errors: Vec<WfError>,
    /// Actual diagnostic-only binder nodes encountered during the full walk.
    pub incomplete_binders: Vec<(FnId, SpanId)>,
}

/// Check all headers, types, modes, bodies and explicit trigger candidates in
/// incomplete source IR. Only the absence of successfully inferred triggers on
/// explicitly diagnostic node variants is suspended. Ordinary binders retain
/// their complete trigger requirements. Every other check runs unchanged.
#[must_use]
pub fn check_crate_for_diagnostics(krate: &VcCrate) -> DiagnosticWf {
    check_crate_impl(krate, true)
}

fn check_crate_impl(krate: &VcCrate, diagnostics: bool) -> DiagnosticWf {
    let mut errors = Vec::new();
    let mut incomplete_binders = Vec::new();
    let mut fns: HashMap<FnId, &FnDecl> = HashMap::new();
    for decl in &krate.fns {
        if fns.insert(decl.id, decl).is_some() {
            errors.push(WfError {
                class: WfClass::Malformed,
                function: Some(decl.id),
                span: decl.span,
                message: format!("function id of `{}` is used twice", decl.name),
            });
        }
    }
    let mut adts: HashMap<AdtId, &AdtDecl> = HashMap::new();
    for adt in &krate.adts {
        if adts.insert(adt.id, adt).is_some() {
            errors.push(WfError {
                class: WfClass::Malformed,
                function: None,
                span: adt.span,
                message: format!("data type id of `{}` is used twice", adt.name),
            });
        }
    }
    let mut projections = HashMap::new();
    for declaration in &krate.projections {
        if declaration.arity == 0
            || projections.insert(declaration.id, declaration).is_some()
        {
            errors.push(WfError {
                class: WfClass::Malformed,
                function: None,
                span: declaration.span,
                message: "an associated-type constructor has zero arguments or a duplicate identity"
                    .into(),
            });
        }
    }
    let projection_definitions = crate::projection_types::Definitions::checked(krate, &mut crate::copy_context::WF_WORK);
    let invalid_projection_definitions = projection_definitions.is_none();
    let index = Index {
        fns,
        adts,
        projections,
        projection_definitions,
        validated_instance_origins: OnceCell::new(),
        source: krate,
        recursive: krate
            .rec_groups
            .iter()
            .flat_map(|group| group.members.iter().map(|(id, _)| *id))
            .collect(),
        architecture: krate.architecture,
    };
    if invalid_projection_definitions {
        errors.push(WfError { class: WfClass::Malformed, function: None,
            span: krate.projection_impls.first().map_or(SpanId(0), |definition| definition.span),
            message: "invalid, ambiguous, cyclic or unrepresented closed associated implementation".into() });
    }
    if krate.architecture.cases().is_err() {
        errors.push(WfError {
            class: WfClass::Malformed,
            function: None,
            span: SpanId(0),
            message: "invalid verification architecture".into(),
        });
    }
    if !matches!(krate.pointer_width, 16 | 32 | 64) {
        errors.push(WfError {
            class: WfClass::Malformed,
            function: None,
            span: SpanId(0),
            message: format!("pointer width {} is not 16, 32 or 64", krate.pointer_width),
        });
    }
    for adt in &krate.adts {
        check_adt(&index, adt, &mut errors);
    }
    check_rec_groups(&index, krate, &mut errors);
    for decl in &krate.fns {
        let mark = errors.len();
        let transport_locals = value_modes::transport_locals(&index, decl);
        let mut checker = FnChecker {
            index: &index,
            decl,
            errors: &mut errors,
            sites: HashSet::new(),
            loops: Vec::new(),
            loop_ids: HashSet::new(),
            proof_in_spec: false,
            diagnostics,
            incomplete_binders: &mut incomplete_binders,
            transport_locals: &transport_locals,
            copy_work: Cell::new(crate::copy_context::WF_WORK),
        };
        checker.check();
        // Value modes are a separate obligation from type checking and the
        // placement of runtime arithmetic checks. Do not add secondary mode
        // errors to a structurally rejected source function.
        if errors.len() == mark {
            errors.extend(value_modes::check(&index, decl, &transport_locals));
        }
        errors.extend(crate::prophecy::check_function(&index.fns, decl));
        // The user errors of an instance are those of its generic function,
        // which reports them itself.
        if decl.role == FnRole::Instance {
            let mut index = mark;
            while index < errors.len() {
                if errors[index].class == WfClass::User {
                    errors.remove(index);
                } else {
                    index += 1;
                }
            }
        }
    }
    DiagnosticWf {
        errors,
        incomplete_binders,
    }
}

/// Lookup tables shared by every function check.
struct Index<'a> {
    fns: HashMap<FnId, &'a FnDecl>,
    adts: HashMap<AdtId, &'a AdtDecl>,
    projections: HashMap<ProjectionId, &'a ProjectionDecl>,
    projection_definitions: Option<crate::projection_types::Definitions<'a>>,
    validated_instance_origins: OnceCell<HashSet<FnId>>,
    source: &'a VcCrate,
    recursive: HashSet<FnId>,
    architecture: crate::bitvector::Architecture,
}

impl Index<'_> {
    /// Is `ty` well formed where `n_params` type parameters are in scope?
    /// Returns a description of the first problem.
    fn ty_problem(&self, ty: &Ty, n_params: usize) -> Option<String> {
        match ty {
            Ty::Bool | Ty::Unit => None,
            Ty::Int(range) => {
                (!range.is_valid()).then(|| format!("invalid integer type {range:?}"))
            }
            Ty::Tuple(elems) => {
                if elems.is_empty() {
                    return Some("an empty tuple type must be represented as Unit".to_string());
                }
                elems
                    .iter()
                    .find_map(|elem| self.ty_problem(elem, n_params))
            }
            Ty::Adt(id, args) => match self.adts.get(id) {
                None => Some(format!("unknown data type {id:?}")),
                Some(adt) if adt.type_params.len() != args.len() => Some(format!(
                    "`{}` takes {} type arguments, not {}",
                    adt.name,
                    adt.type_params.len(),
                    args.len()
                )),
                Some(_) => args.iter().find_map(|arg| self.ty_problem(arg, n_params)),
            },
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => self.ty_problem(inner, n_params),
            Ty::Projection(id, args) => match self.projections.get(id) {
                None => Some(format!("unknown associated-type constructor {id:?}")),
                Some(declaration) if declaration.arity != args.len() => Some(format!(
                    "associated-type constructor `{}` takes {} arguments, not {}",
                    declaration.name, declaration.arity, args.len()
                )),
                Some(_) => args.iter().find_map(|arg| self.ty_problem(arg, n_params)),
            },
            Ty::Param(n) => {
                ((*n as usize) >= n_params).then(|| format!("type parameter {n} is not in scope"))
            }
        }
    }
}

/// Groups of recursive functions: known functions that are not instances,
/// each in one group at most, with cycles of length 1 or more.
fn check_rec_groups(index: &Index<'_>, krate: &VcCrate, errors: &mut Vec<WfError>) {
    let mut seen: HashSet<FnId> = HashSet::new();
    for group in &krate.rec_groups {
        for (id, cycle) in &group.members {
            let mut report = |span: SpanId, message: String| {
                errors.push(WfError {
                    class: WfClass::Malformed,
                    function: Some(*id),
                    span,
                    message,
                });
            };
            let Some(decl) = index.fns.get(id) else {
                report(
                    SpanId(0),
                    format!("recursive group member {id:?} does not exist"),
                );
                continue;
            };
            if !seen.insert(*id) {
                report(
                    decl.span,
                    format!("`{}` is in two recursive groups", decl.name),
                );
            }
            if decl.role == FnRole::Instance {
                report(
                    decl.span,
                    format!("instance `{}` in a recursive group", decl.name),
                );
            }
            if decl.role == FnRole::Imported {
                report(
                    decl.span,
                    "an imported declaration cannot belong to a recursive group".into(),
                );
            }
            if *cycle == 0 {
                report(
                    decl.span,
                    format!("`{}` has a cycle of length 0", decl.name),
                );
            }
        }
    }
}

fn check_adt(index: &Index<'_>, adt: &AdtDecl, errors: &mut Vec<WfError>) {
    let mut report = |message: String| {
        errors.push(WfError {
            class: WfClass::Malformed,
            function: None,
            span: adt.span,
            message,
        });
    };
    if adt.kind == AdtKind::Struct && adt.variants.len() != 1 {
        report(format!(
            "struct `{}` must have exactly one variant",
            adt.name
        ));
    }
    if adt.kind == AdtKind::Opaque && !adt.variants.is_empty() {
        report(format!(
            "opaque carrier `{}` must not expose variants or fields",
            adt.name
        ));
    }
    for variant in &adt.variants {
        for field in &variant.fields {
            if let Some(problem) = index.ty_problem(&field.ty, adt.type_params.len()) {
                report(format!(
                    "field `{}` of `{}`: {problem}",
                    field.name, adt.name
                ));
            }
        }
    }
}

/// Where statements run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Context {
    /// Exec code outside ghost blocks: exec checks allowed.
    Exec,
    /// Proof code: a proof function body or a ghost block.
    Proof,
    /// Physical Exec syntax under a Spec condition: logical Proof effects,
    /// but body-code checks may be evaluated by explicit checked declarations.
    ExecProof,
    /// Explicit ghost code nested under Spec-controlled physical Exec.
    SpecProof,
}

impl Context {
    const fn physical_exec(self) -> bool {
        matches!(self, Self::Exec | Self::ExecProof)
    }

    const fn spec_controlled(self) -> bool {
        matches!(self, Self::ExecProof | Self::SpecProof)
    }

    const fn ghost(self) -> Self {
        if self.spec_controlled() {
            Self::SpecProof
        } else {
            Self::Proof
        }
    }

    const fn mode(self) -> Mode {
        match self {
            Self::Exec => Mode::Exec,
            Self::Proof | Self::ExecProof | Self::SpecProof => Mode::Proof,
        }
    }
}

struct FnChecker<'a, 'e> {
    index: &'a Index<'a>,
    decl: &'a FnDecl,
    errors: &'e mut Vec<WfError>,
    sites: HashSet<SiteId>,
    /// The loops around the statement being checked, innermost last.
    loops: Vec<LoopId>,
    /// Every loop id seen so far.
    loop_ids: HashSet<LoopId>,
    /// Where a `ProofInSpec` may appear: the body of a spec function with a
    /// measure, outside another one.
    proof_in_spec: bool,
    diagnostics: bool,
    incomplete_binders: &'e mut Vec<(FnId, SpanId)>,
    transport_locals: &'e [bool],
    copy_work: Cell<usize>,
}

impl FnChecker<'_, '_> {
    fn substituted_type_matches(&self, formal: &Ty, arguments: Option<&[Ty]>, actual: &Ty) -> bool {
        let Some(definitions) = &self.index.projection_definitions else { return false; };
        if definitions.is_empty() {
            return match arguments {
                Some(arguments) => crate::copy_context::matches_substitution_with(formal, arguments, actual,
                    |amount| self.copy_charge(amount)) == Ok(true),
                None => formal == actual,
            };
        }
        let mut remaining = self.copy_work.get();
        let result = definitions.equal_substitution(formal, arguments, actual, &mut remaining).unwrap_or(false);
        self.copy_work.set(remaining);
        result
    }

    fn copy_charge(&self, amount: usize) -> Result<(), ()> {
        match self.copy_work.get().checked_sub(amount) {
            Some(left) => {
                self.copy_work.set(left);
                Ok(())
            }
            None => {
                self.copy_work.set(0);
                Err(())
            }
        }
    }

    fn normalized_copy_type(&self, ty: &Ty, arguments: Option<&[Ty]>) -> Result<Ty, ()> {
        let definitions = self.index.projection_definitions.as_ref().ok_or(())?;
        let mut remaining = self.copy_work.get();
        let result = match arguments {
            Some(arguments) => definitions.substitute(ty, arguments, &mut remaining),
            None => definitions.normalize(ty, &mut remaining),
        };
        self.copy_work.set(remaining);
        result.ok_or(())
    }

    fn check_copy_premises(&mut self) {
        let declaration = self.decl;
        for premise in &declaration.copy_premises {
            match crate::copy_context::wellformed_with(
                &self.index.adts,
                &|id| self.index.projections.get(&id).map(|decl| decl.arity),
                premise,
                declaration.type_params.len(),
                |n| self.copy_charge(n),
            ) {
                Ok(true) => {}
                Ok(false) => {
                    self.malformed(
                        declaration.span,
                        "an invalid Copy premise type or parameter scope",
                    );
                    continue;
                }
                Err(()) => {
                    self.malformed(declaration.span, "Copy typing work exhausted");
                    continue;
                }
            }
            let normalized = if self.index.projection_definitions.as_ref().is_some_and(|definitions| !definitions.is_empty()) {
                match self.normalized_copy_type(premise, None) {
                    Ok(ty) => Some(ty),
                    Err(()) => { self.malformed(declaration.span, "Copy normalization work or declaration exhausted"); continue; }
                }
            } else { None };
            match crate::copy_context::admissible_with(&self.index.adts, normalized.as_ref().unwrap_or(premise), |n| self.copy_charge(n)) {
                Ok(true) => {}
                Ok(false) => self.malformed(self.decl.span, "a Copy premise has a mutable-reference, unknown, opaque or recursive rigid layout"),
                Err(()) => self.malformed(self.decl.span, "Copy typing work exhausted"),
            }
        }
    }

    fn discharge_copy(&mut self, target: &FnDecl, arguments: &[Ty], span: SpanId, closed: bool) {
        // A concrete instance may not authorize its own ground assumptions.
        let declaration = self.decl;
        let premises = if closed {
            &[][..]
        } else {
            declaration.copy_premises.as_slice()
        };
        if self.index.projection_definitions.as_ref().is_some_and(|definitions| !definitions.is_empty()) {
            if self.copy_charge(premises.len()).is_err() {
                self.malformed(span, "Copy typing work exhausted"); return;
            }
            let normalized = premises.iter().map(|ty| self.normalized_copy_type(ty, None)).collect::<Result<Vec<_>, _>>();
            let Ok(normalized) = normalized else {
                self.malformed(span, "Copy normalization work or declaration exhausted"); return;
            };
            for premise in &target.copy_premises {
                let Ok(actual) = self.normalized_copy_type(premise, Some(arguments)) else {
                    self.malformed(span, "Copy normalization work or declaration exhausted"); return;
                };
                match crate::copy_context::is_copy_with(&self.index.adts, &normalized, &actual, None, |n| self.copy_charge(n)) {
                    Ok(true) => {}
                    Ok(false) => self.malformed(span, "a target Copy premise is not discharged by the caller typing context"),
                    Err(()) => self.malformed(span, "Copy typing work exhausted"),
                }
            }
            return;
        }
        for premise in &target.copy_premises {
            match crate::copy_context::is_copy_with(
                &self.index.adts,
                premises,
                premise,
                Some(arguments),
                |n| self.copy_charge(n),
            ) {
                Ok(true) => {}
                Ok(false) => self.malformed(
                    span,
                    "a target Copy premise is not discharged by the caller typing context",
                ),
                Err(()) => self.malformed(span, "Copy typing work exhausted"),
            }
        }
    }
    fn report(&mut self, class: WfClass, span: SpanId, message: impl Into<String>) {
        self.errors.push(WfError {
            class,
            function: Some(self.decl.id),
            span,
            message: message.into(),
        });
    }

    fn malformed(&mut self, span: SpanId, message: impl Into<String>) {
        let message = format!("in `{}`: {}", self.decl.name, message.into());
        self.report(WfClass::Malformed, span, message);
    }

    fn local(&self, local: LocalId) -> Option<&crate::item::LocalDecl> {
        self.decl.local(local)
    }

    fn use_site(&mut self, site: SiteId, span: SpanId) {
        if !self.sites.insert(site) {
            self.malformed(span, format!("site {} is used twice", site.0));
        }
    }

    fn check_instance_origin(&mut self) {
        let Some(origin) = &self.decl.attrs.instance else {
            return;
        };
        let decl = self.decl;
        let Some(original) = self.index.fns.get(&origin.declaration).copied() else {
            self.malformed(decl.span, "an instance has no original declaration");
            return;
        };
        if decl.role != FnRole::Instance
            || original.role == FnRole::Instance
            || original.role == FnRole::Imported
            || original.attrs.instance.is_some()
            || !decl.type_params.is_empty()
            || origin.type_args.len() != original.type_params.len()
            || origin.type_args.iter().any(Ty::has_param)
        {
            self.malformed(
                decl.span,
                "an invalid generic instance origin or substitution",
            );
            return;
        }
        for arg in &origin.type_args {
            if let Some(problem) = self.index.ty_problem(arg, 0) {
                self.malformed(decl.span, problem);
                return;
            }
        }
        self.discharge_copy(original, &origin.type_args, decl.span, true);
        let mut premises_match = decl.copy_premises.len() == original.copy_premises.len();
        for (formal, actual) in original.copy_premises.iter().zip(&decl.copy_premises) {
            premises_match &= self.substituted_type_matches(formal, Some(&origin.type_args), actual);
        }
        if !premises_match {
            self.malformed(
                decl.span,
                "an instance Copy context disagrees with its native origin",
            );
        }
        let parameters_match = decl.params.len() == original.params.len()
            && decl
                .params
                .iter()
                .zip(&original.params)
                .all(
                    |(actual, formal)| match (decl.local(*actual), original.local(*formal)) {
                        (Some(actual), Some(formal)) => {
                            self.substituted_type_matches(&formal.ty, Some(&origin.type_args), &actual.ty)
                                && actual.mode == formal.mode
                                && actual.mutable == formal.mutable
                                && actual.prophecy == formal.prophecy
                        }
                        _ => false,
                    },
                );
        let result_matches = match (decl.local(decl.ret), original.local(original.ret)) {
            (Some(actual), Some(formal)) => {
                self.substituted_type_matches(&formal.ty, Some(&origin.type_args), &actual.ty)
                    && actual.mode == formal.mode
                    && actual.prophecy == formal.prophecy
            }
            _ => false,
        };
        let attrs = decl.attrs.without_instance();
        if decl.mode != original.mode
            || decl.kind != original.kind
            || attrs != original.attrs
            || !parameters_match
            || !result_matches
            || !crate::instance_semantics::unwind_matches(
                &self.index.fns,
                original,
                decl,
                &self.index.validated_instance_origins,
                self.index.projection_definitions.as_ref(),
            )
        {
            self.malformed(
                decl.span,
                "an instance signature disagrees with its native origin",
            );
        }
    }

    fn check(&mut self) {
        let decl = self.decl;
        self.check_copy_premises();
        self.check_instance_origin();
        if decl.attrs.inline {
            if decl.mode != Mode::Spec {
                self.report(
                    WfClass::User,
                    decl.span,
                    "'inline' is only allowed for 'spec' functions",
                );
            }
            if !decl.decreases.is_empty() || self.index.recursive.contains(&decl.id) {
                self.report(
                    WfClass::User,
                    decl.span,
                    "'inline' functions cannot be recursive",
                );
            }
            if !matches!(decl.body, Body::Spec(_)) {
                self.report(
                    WfClass::User,
                    decl.span,
                    "'inline' functions must have a body",
                );
            }
        }
        match decl.kind {
            FnKind::Function | FnKind::ConstFunction => {}
            FnKind::Constant(ConstMode::Spec) => {
                if decl.mode != Mode::Spec
                    || decl
                        .local(decl.ret)
                        .is_none_or(|ret| ret.mode != Mode::Spec)
                {
                    self.malformed(
                        decl.span,
                        "a spec constant must have spec declaration and return modes",
                    );
                }
                if !decl.params.is_empty() || decl.role == FnRole::TraitDecl {
                    self.malformed(
                        decl.span,
                        "a constant cannot have parameters or be a trait function declaration",
                    );
                }
                if !decl.requires.is_empty() || !decl.recommends.is_empty() {
                    self.report(
                        WfClass::User,
                        decl.span,
                        "consts cannot have requires/recommends",
                    );
                }
                if !decl.ensures.is_empty() {
                    self.report(
                        WfClass::User,
                        decl.span,
                        "const cannot have `ensures` unless it is `exec const`",
                    );
                }
                if !decl.decreases.is_empty()
                    || decl.decreases_when.is_some()
                    || decl.decreases_by.is_some()
                {
                    self.malformed(
                        decl.span,
                        "constant declarations cannot carry function termination clauses",
                    );
                }
            }
            FnKind::Constant(ConstMode::Dual) => {
                if decl.mode != Mode::Spec
                    || decl
                        .local(decl.ret)
                        .is_none_or(|ret| ret.mode != Mode::Exec)
                    || !decl.params.is_empty()
                    || !matches!(decl.body, Body::Constant(_) | Body::None)
                    || !decl.requires.is_empty()
                    || !decl.recommends.is_empty()
                    || !decl.ensures.is_empty()
                    || !decl.decreases.is_empty()
                    || decl.decreases_when.is_some()
                    || decl.decreases_by.is_some()
                    || decl.attrs.inline
                {
                    self.malformed(decl.span, "a dual constant needs a parameter-free checked initializer and exec result");
                }
                if decl.body == Body::None
                    && decl.role != FnRole::TraitDecl
                    && !decl.attrs.external_body
                {
                    self.malformed(decl.span, "a dual constant without its initializer");
                }
            }
            FnKind::Constant(ConstMode::Exec) | FnKind::Static => {
                if decl.mode != Mode::Exec
                    || decl
                        .local(decl.ret)
                        .is_none_or(|ret| ret.mode != Mode::Exec)
                    || !decl.params.is_empty()
                    || matches!(decl.role, FnRole::TraitDecl | FnRole::Imported)
                    || !matches!(decl.body, Body::Stmts(_) | Body::None)
                    || !decl.requires.is_empty()
                    || !decl.recommends.is_empty()
                    || !decl.decreases.is_empty()
                    || decl.decreases_when.is_some()
                    || decl.decreases_by.is_some()
                    || decl.attrs.inline
                    || decl.body == Body::None && !decl.attrs.external_body
                {
                    self.malformed(decl.span, "an executable value needs a parameter-free checked initializer, exec result and no function preconditions");
                }
                if decl.kind == FnKind::Static {
                    // One original Static WF allowance: storage and complete
                    // dependency admission share it, including failed work.
                    let static_work = Cell::new(100_000);
                    if !decl.type_params.is_empty()
                        || decl.role != FnRole::Item
                        || !decl.copy_premises.is_empty()
                        || decl.ret_ty().is_none_or(|ty| {
                            !crate::static_values::storage_type_budgeted(
                                ty,
                                &self.index.adts,
                                &static_work,
                            )
                        })
                    {
                        self.malformed(decl.span, "static storage must be monomorphic represented data without owned abstract or mutable-reference slots");
                    }
                    if self.index.recursive.contains(&decl.id) {
                        self.malformed(
                            decl.span,
                            "static initializer contracts cannot belong to a recursive group",
                        );
                    }
                    if let Err(problem) = crate::static_values::dependency_problem(
                        self.index.source,
                        &self.index.fns,
                        &self.index.adts,
                        decl.id,
                        &static_work,
                    ) {
                        self.malformed(decl.span, problem);
                    }
                }
            }
        }
        match decl.role {
            FnRole::Item => {}
            FnRole::TraitDecl if decl.type_params.is_empty() => {
                self.malformed(decl.span, "a trait method declaration without `Self`");
            }
            FnRole::TraitDecl => {}
            FnRole::Instance if !decl.type_params.is_empty() => {
                self.malformed(decl.span, "an instance with type parameters");
            }
            FnRole::Instance => {}
            FnRole::Imported => {
                if let Some(problem) = decl.imported_problem() {
                    self.malformed(decl.span, problem);
                }
            }
        }
        for (index, local) in decl.locals.iter().enumerate() {
            if let Some(problem) = self.index.ty_problem(&local.ty, decl.type_params.len()) {
                self.malformed(
                    local.span,
                    format!("local `{}` ({index}): {problem}", local.name),
                );
            }
        }
        self.check_signature();
        if let Some(problem) = decl.broadcast_problem() {
            self.malformed(decl.span, problem);
        }
        for hint in decl.broadcast_hints() {
            self.check_expr(hint, false);
        }

        if decl.mode == Mode::Spec {
            for param in &decl.params {
                if let Some(local) = self.local(*param) {
                    if local.mutable {
                        let span = local.span;
                        self.report(WfClass::User, span, MSG_MUT_SPEC_PARAM);
                    }
                }
            }
        }

        for clause in &decl.requires {
            self.check_clause(clause, false);
        }
        for clause in &decl.ensures {
            self.check_clause(clause, true);
        }
        for clause in &decl.recommends {
            self.check_clause(clause, false);
        }
        self.check_termination_clauses();
        self.check_unwind();

        let ret_ty = decl.ret_ty().cloned().unwrap_or(Ty::Unit);
        match (&decl.body, decl.mode) {
            (Body::None, _) => {}
            (Body::Constant(expr), _) => {
                if decl.kind != FnKind::Constant(ConstMode::Dual) {
                    self.malformed(
                        expr.span,
                        "an initializer on a declaration that is not a dual constant",
                    );
                }
                self.check_expr(expr, true);
                self.check_initializer(expr);
                if expr.ty != ret_ty {
                    self.malformed(
                        expr.span,
                        "a constant initializer differs from its declared result type",
                    );
                }
            }
            (Body::Spec(expr), Mode::Spec) => {
                self.proof_in_spec = !decl.decreases.is_empty();
                self.check_expr(expr, false);
                self.proof_in_spec = false;
                if expr.ty != ret_ty {
                    self.malformed(
                        expr.span,
                        "spec function body does not have the return type",
                    );
                }
            }
            (Body::Spec(expr), _) => {
                self.malformed(
                    expr.span,
                    "an exec or proof function has an expression body",
                );
            }
            (Body::Stmts(block), Mode::Spec) => match first_assignment(block) {
                Some(span) => self.report(WfClass::User, span, MSG_ASSIGN_IN_PURE),
                None => self.malformed(decl.span, "a spec function has a statement body"),
            },
            (Body::Stmts(block), Mode::Exec) => self.check_block(block, Context::Exec),
            (Body::Stmts(block), Mode::Proof) => self.check_block(block, Context::Proof),
        }
    }

    /// `decreases`, `when` and `via`: integer measures over the
    /// parameters, a `bool` condition on a spec function with a measure, and
    /// a `#[verifier::decreases_by]` proof function with the same parameters.
    fn check_termination_clauses(&mut self) {
        let decl = self.decl;
        for measure in &decl.decreases {
            self.check_expr(measure, false);
            if measure.ty.int_range().is_none() {
                self.malformed(measure.span, "a decreases measure that is not an integer");
            }
            if mentions_local(measure, decl.ret) {
                self.malformed(measure.span, "a decreases measure reads the return value");
            }
        }
        if let Some(when) = &decl.decreases_when {
            self.check_bool(when, false);
            if decl.mode != Mode::Spec || decl.decreases.is_empty() {
                self.malformed(
                    when.span,
                    "a decreases_when on a function that is not spec or has no measure",
                );
            }
        }
        if let Some(via) = decl.decreases_by {
            if decl.mode != Mode::Spec {
                self.malformed(decl.span, "decreases_by on a function that is not spec");
            }
            let Some(proof) = self.index.fns.get(&via).copied() else {
                self.malformed(decl.span, "decreases_by of an unknown function");
                return;
            };
            if proof.mode != Mode::Proof || !proof.attrs.is_decreases_by {
                self.malformed(
                    decl.span,
                    "decreases_by of a function that is not a decreases_by proof function",
                );
            }
            let types = |d: &FnDecl| -> Vec<Option<Ty>> {
                d.params
                    .iter()
                    .map(|p| d.local(*p).map(|l| l.ty.clone()))
                    .collect()
            };
            if types(proof) != types(decl) || proof.type_params.len() != decl.type_params.len() {
                self.malformed(
                    decl.span,
                    "a decreases_by function whose parameters differ from the function's",
                );
            }
        }
    }

    fn check_initializer(&mut self, expression: &Expr) {
        match &expression.kind {
            ExprKind::Call { callee, .. }
                if self
                    .index
                    .fns
                    .get(callee)
                    .is_none_or(|target| target.kind != FnKind::Constant(ConstMode::Dual)) =>
            {
                self.malformed(
                    expression.span,
                    "a dual initializer may read only dual constants, not call functions",
                );
            }
            ExprKind::Read(place)
                if self
                    .local(place.local)
                    .is_none_or(|local| local.mode != Mode::Exec) =>
            {
                self.malformed(expression.span, "a dual initializer reads a non-exec value");
            }
            ExprKind::Old(_)
            | ExprKind::Quant { .. }
            | ExprKind::Choose { .. }
            | ExprKind::UntriggeredQuant { .. }
            | ExprKind::UntriggeredChoose { .. }
            | ExprKind::ProofInSpec(_)
            | ExprKind::ProofInSpecTail { .. }
            | ExprKind::MutRefCurrent(_)
            | ExprKind::MutRefFuture(_)
            | ExprKind::MutRefUpdate { .. }
            | ExprKind::HasResolved(_) => {
                self.malformed(expression.span, "a ghost expression in a dual initializer")
            }
            _ => {}
        }
        expression.for_each_child(&mut |child| self.check_initializer(child));
    }

    fn check_signature(&mut self) {
        let decl = self.decl;
        let mut seen = HashSet::new();
        for param in &decl.params {
            match self.local(*param).map(|local| local.kind) {
                Some(LocalKind::Param) => {
                    if !seen.insert(*param) {
                        self.malformed(decl.span, format!("parameter {} is listed twice", param.0));
                    }
                }
                Some(_) => self.malformed(
                    decl.span,
                    format!("local {} is listed as a parameter", param.0),
                ),
                None => self.malformed(decl.span, format!("parameter {} does not exist", param.0)),
            }
        }
        for (index, local) in decl.locals.iter().enumerate() {
            let id = LocalId(u32::try_from(index).unwrap_or(u32::MAX));
            if local.kind == LocalKind::Param && !seen.contains(&id) {
                self.malformed(
                    local.span,
                    format!("parameter `{}` is not in the parameter list", local.name),
                );
            }
            if local.kind == LocalKind::Return && id != decl.ret {
                self.malformed(
                    local.span,
                    format!("`{}` is a second return local", local.name),
                );
            }
        }
        match self.local(decl.ret).map(|local| local.kind) {
            Some(LocalKind::Return) => {}
            _ => self.malformed(
                decl.span,
                "the return local is missing or has the wrong kind",
            ),
        }
    }

    fn check_attrs(&mut self, attrs: &ClauseAttrs, span: SpanId) {
        if attrs.proof_notes.len() > 1 || attrs.custom_errs.len() > 1 {
            self.report(WfClass::User, span, MSG_DUPLICATE_NOTE);
        }
    }

    fn check_clause(&mut self, clause: &Clause, may_read_return: bool) {
        self.check_attrs(&clause.attrs, clause.span);
        self.check_bool(&clause.expr, false);
        if !may_read_return && mentions_local(&clause.expr, self.decl.ret) {
            self.malformed(clause.span, "a precondition reads the return value");
        }
    }

    fn check_bool(&mut self, expr: &Expr, checks_allowed: bool) {
        self.check_expr(expr, checks_allowed);
        if expr.ty != Ty::Bool {
            self.malformed(expr.span, "condition is not a bool");
        }
    }

    // ------------------------------------------------------------------
    // Statements
    // ------------------------------------------------------------------

    fn check_block(&mut self, block: &Block, cx: Context) {
        for stmt in &block.stmts {
            self.check_stmt(stmt, cx);
        }
    }

    /// A declaration's check placement never changes its stored value mode.
    fn check_let(
        &mut self,
        local: LocalId,
        init: Option<&Expr>,
        span: SpanId,
        cx: Context,
        checked: bool,
    ) {
        let Some(decl) = self.local(local).cloned() else {
            self.malformed(span, format!("let of missing local {}", local.0));
            return;
        };
        if !matches!(decl.kind, LocalKind::Let | LocalKind::Temp) {
            self.malformed(
                span,
                format!("let of `{}`, which is not a let local", decl.name),
            );
        }
        if cx.mode() == Mode::Proof && decl.mode == Mode::Exec {
            self.malformed(
                span,
                format!("exec local `{}` declared in proof code", decl.name),
            );
        }
        if checked && (!cx.physical_exec() || decl.mode != Mode::Spec) {
            self.malformed(
                span,
                "a checked initializer requires Exec context and Spec storage",
            );
        }
        if let Some(init) = init {
            self.check_expr(
                init,
                cx.physical_exec() && (checked || (cx == Context::Exec && decl.mode == Mode::Exec)),
            );
            if init.ty != decl.ty {
                self.malformed(
                    init.span,
                    format!("initialiser of `{}` has the wrong type", decl.name),
                );
            }
        }
    }

    fn check_stmt(&mut self, stmt: &Stmt, cx: Context) {
        let exec = cx == Context::Exec;
        match &stmt.kind {
            StmtKind::Let { local, init } => {
                self.check_let(*local, init.as_ref(), stmt.span, cx, false);
            }
            StmtKind::LetChecked { local, init } => {
                self.check_let(*local, Some(init), stmt.span, cx, true);
            }
            StmtKind::Assign { place, value } => {
                let target_mode = self.check_assignable(place, stmt.span, cx);
                self.check_expr(value, exec && target_mode == Some(Mode::Exec));
                if let Some(place_ty) = self.place_ty(place, stmt.span) {
                    if place_ty != value.ty {
                        self.malformed(value.span, "assigned value has the wrong type");
                    }
                }
            }
            StmtKind::AssignSpec { place, value } => {
                if !cx.physical_exec() {
                    self.malformed(
                        stmt.span,
                        "a checked Spec assignment outside physical Exec code",
                    );
                }
                let target_mode = self.check_assignable(place, stmt.span, cx.ghost());
                if target_mode != Some(Mode::Spec) {
                    self.malformed(stmt.span, "a checked Spec assignment requires Spec storage");
                }
                self.check_expr(value, cx.physical_exec());
                if let Some(place_ty) = self.place_ty(place, stmt.span) {
                    if place_ty != value.ty {
                        self.malformed(value.span, "assigned value has the wrong type");
                    }
                }
            }
            StmtKind::Call {
                callee,
                type_args,
                args,
                dest,
                site,
            } => self.check_call_stmt(
                stmt.span,
                cx,
                *callee,
                type_args,
                args,
                dest.as_ref(),
                *site,
            ),
            StmtKind::Assert { expr, site, attrs } => {
                self.use_site(*site, stmt.span);
                self.check_attrs(attrs, stmt.span);
                self.check_bool(expr, false);
            }
            StmtKind::AssertBitVector {
                requires,
                ensures,
                architecture,
                site,
            } => {
                self.use_site(*site, stmt.span);
                if cx.mode() != Mode::Proof {
                    self.malformed(stmt.span, "an isolated BV assertion outside proof code");
                }
                if architecture.cases().is_err() {
                    self.malformed(stmt.span, "an invalid isolated BV architecture");
                }
                if *architecture != self.index.architecture {
                    self.malformed(
                        stmt.span,
                        "an isolated BV assertion with a different source architecture",
                    );
                }
                if ensures.is_empty() {
                    self.malformed(stmt.span, "an isolated BV assertion without ensures");
                }
                for clause in requires.iter().chain(ensures) {
                    self.check_attrs(&clause.attrs, clause.span);
                    self.check_bool(&clause.expr, false);
                }
            }
            StmtKind::BorrowMut { dest, place } => {
                let source_mode = self.check_storage_access(place, stmt.span, cx, true);
                let result_mode = source_mode.map(|mode| crate::place_mode::join(mode, cx.mode()));
                let dest_decl = self.local(*dest).cloned();
                if dest_decl.as_ref().is_none_or(|dest| {
                    dest.mode == Mode::Spec
                        || (result_mode.is_some() && Some(dest.mode) != result_mode)
                        || !matches!(dest.kind, LocalKind::Let | LocalKind::Temp)
                }) {
                    self.malformed(stmt.span,"a mutable storage borrow requires an owned destination with the derived reference mode");
                }
                let source_ty = self.place_ty(place, stmt.span);
                let dest_ty = self.local(*dest).map(|local| local.ty.clone());
                if source_ty
                    .as_ref()
                    .map(|ty| Ty::MutRef(Box::new(ty.clone())))
                    != dest_ty
                {
                    self.malformed(
                        stmt.span,
                        "a mutable-borrow destination has the wrong opaque reference type",
                    );
                }
                if self.proof_in_spec {
                    self.malformed(
                        stmt.span,
                        "mutable storage borrowing inside a pure spec expression",
                    );
                }
            }
            StmtKind::Assume { expr, attrs } => {
                self.check_attrs(attrs, stmt.span);
                self.check_bool(expr, false);
            }
            StmtKind::If {
                cond,
                then_block,
                else_block,
            } => {
                self.check_bool(cond, cx.physical_exec());
                self.check_block(then_block, cx);
                self.check_block(else_block, cx);
            }
            StmtKind::IfSpec {
                cond,
                then_block,
                else_block,
            } => {
                if !cx.physical_exec() {
                    self.malformed(
                        stmt.span,
                        "a Spec-controlled conditional outside physical Exec code",
                    );
                }
                self.check_bool(cond, cx.physical_exec());
                let branch = if cx.physical_exec() {
                    Context::ExecProof
                } else {
                    Context::Proof
                };
                self.check_block(then_block, branch);
                self.check_block(else_block, branch);
            }
            StmtKind::Return { value, site } => {
                self.use_site(*site, stmt.span);
                if cx.spec_controlled() && self.decl.mode == Mode::Exec {
                    self.report(
                        WfClass::User,
                        stmt.span,
                        "cannot return from exec function in spec-controlled code",
                    );
                }
                let ret_ty = self.decl.ret_ty().cloned().unwrap_or(Ty::Unit);
                match value {
                    Some(value) => {
                        let return_exec = self
                            .decl
                            .local(self.decl.ret)
                            .is_some_and(|ret| ret.mode == Mode::Exec);
                        self.check_expr(value, exec && return_exec);
                        if value.ty != ret_ty {
                            self.malformed(value.span, "returned value has the wrong type");
                        }
                    }
                    None => {
                        if ret_ty != Ty::Unit {
                            self.malformed(stmt.span, "a function with a result returns nothing");
                        }
                    }
                }
            }
            StmtKind::Reveal { callee, .. } | StmtKind::Hide { callee } => {
                match self.index.fns.get(callee) {
                    Some(decl) if decl.role == FnRole::Imported => self.malformed(
                        stmt.span,
                        "reveal or hide of an imported signature without body authority",
                    ),
                    Some(decl) if decl.mode == Mode::Spec => {}
                    Some(_) => {
                        self.malformed(stmt.span, "reveal or hide of a function that is not spec")
                    }
                    None => self.malformed(stmt.span, "reveal or hide of an unknown function"),
                }
            }
            StmtKind::BroadcastUse { callee } => match self.index.fns.get(callee) {
                Some(decl)
                    if decl.attrs.broadcast_triggers.is_some()
                        && decl.broadcast_problem().is_none() => {}
                _ => self.malformed(
                    stmt.span,
                    "broadcast use of an unsupported or unknown local broadcast proof",
                ),
            },
            StmtKind::Ghost(block) => self.check_block(block, cx.ghost()),
            StmtKind::GhostTail { block, tail } => {
                if !cx.physical_exec() {
                    self.malformed(stmt.span, "a proof block tail outside executable code");
                }
                self.check_block(block, cx.ghost());
                self.check_expr(tail, false);
                self.expect_ty(tail, &Ty::Unit, "proof block tail");
            }
            StmtKind::Block(block) => self.check_block(block, cx),
            StmtKind::Loop(lp) => self.check_loop(lp, stmt.span, cx),
            StmtKind::Break { target, site } | StmtKind::Continue { target, site } => {
                self.use_site(*site, stmt.span);
                if cx.spec_controlled() {
                    self.report(
                        WfClass::User,
                        stmt.span,
                        "cannot leave an exec loop from spec-controlled code",
                    );
                }
                if !self.loops.contains(target) {
                    self.malformed(
                        stmt.span,
                        format!(
                            "break or continue of loop {}, which does not enclose it",
                            target.0
                        ),
                    );
                }
            }
            StmtKind::Unreachable => {}
        }
    }

    /// A loop: exec code only, conditions and measures typed, sites unique.
    fn check_loop(&mut self, lp: &Loop, span: SpanId, cx: Context) {
        if cx != Context::Exec {
            self.malformed(span, "a loop in proof code");
        }
        if !self.loop_ids.insert(lp.id) {
            self.malformed(span, format!("loop id {} is used twice", lp.id.0));
        }
        self.use_site(lp.sites.entry, span);
        self.use_site(lp.sites.end, span);
        self.use_site(lp.sites.exit, span);
        if lp.allow_complex_invariants && lp.isolation {
            self.malformed(span, "allow_complex_invariants on an isolated loop");
        }
        let simple = lp
            .invariants
            .iter()
            .all(|inv| inv.kind == InvariantKind::Always);
        if !lp.isolation && !simple && !lp.allow_complex_invariants {
            self.malformed(
                span,
                "a loop without isolation has invariant_except_break or ensures clauses",
            );
        }
        for inv in &lp.invariants {
            self.check_bool(&inv.expr, false);
        }
        for measure in &lp.decreases {
            self.check_expr(measure, false);
            if measure.ty.int_range().is_none() {
                self.malformed(measure.span, "a decreases measure that is not an integer");
            }
        }
        if let Some(cond) = &lp.cond {
            // `break` and `continue` in the condition leave the enclosing loop.
            self.check_block(&cond.block, cx);
            self.check_bool(&cond.expr, true);
        }
        self.loops.push(lp.id);
        self.check_block(&lp.body, cx);
        self.loops.pop();
    }

    /// Check that `place` may be written from `cx`; returns the mode of its
    /// root local.
    fn check_assignable(&mut self, place: &Place, span: SpanId, cx: Context) -> Option<Mode> {
        self.check_storage_access(place, span, cx, false)
    }

    /// Borrowing a place does not grant permission to mutate it from ghost
    /// code. In particular a Proof reference can still point at Exec storage.
    fn check_storage_access(
        &mut self,
        place: &Place,
        span: SpanId,
        cx: Context,
        borrow: bool,
    ) -> Option<Mode> {
        let Some(root) = self.local(place.local).cloned() else {
            self.malformed(
                span,
                format!("assignment to missing local {}", place.local.0),
            );
            return None;
        };
        let through_ref = place.has_deref();
        match root.kind {
            LocalKind::Param if !root.mutable && !through_ref => {
                self.report(WfClass::User, span, msg_not_mutable(&root.name));
            }
            LocalKind::Return | LocalKind::Bound => {
                self.malformed(
                    span,
                    format!("assignment to `{}`, which cannot be assigned", root.name),
                );
            }
            // An immutable `let` without an initialiser may be assigned once;
            // counting assignments is the borrow checker's job.
            _ => {}
        }
        if through_ref {
            let mut ty = root.ty.clone();
            for projection in &place.projections {
                if *projection == Projection::Deref {
                    if let Ty::Ref { mutable: false, .. } = ty {
                        self.malformed(span, "assignment through a shared reference");
                        break;
                    }
                }
                match self.project(&ty, *projection, span) {
                    Some(next) => ty = next,
                    None => break,
                }
            }
        }
        let authority = crate::place_mode::place_mode(self.decl, &self.index.adts, place)?;
        if authority.through_spec_mut_ref {
            self.report(
                WfClass::User,
                span,
                "cannot mutate through a spec-mode mutable reference",
            );
            return None;
        }
        if borrow && authority.mode == Mode::Spec {
            self.report(
                WfClass::User,
                span,
                "cannot take mutable borrow of ghost-mode place",
            );
            return None;
        }
        // An ANF save does not read or borrow the Spec storage. The contextual
        // value pass independently authenticates every producer and consumer.
        let value_transport = !borrow
            && place.projections.is_empty()
            && root.mode == Mode::Spec
            && self.transport_locals.get(place.local.index()) == Some(&true);
        if cx == Context::Exec && !authority.exec_accessible && !value_transport {
            self.report(
                WfClass::User,
                span,
                "cannot access non-exec place in executable code",
            );
        }
        if borrow && cx.spec_controlled() && authority.mode == Mode::Exec {
            self.report(
                WfClass::User,
                span,
                "cannot mutably borrow exec storage from spec-controlled code",
            );
        }
        if !borrow && cx.mode() == Mode::Proof && authority.mode == Mode::Exec {
            self.report(
                WfClass::User,
                span,
                format!(
                    "cannot assign to exec variable from {} mode",
                    cx.mode().name()
                ),
            );
        }
        Some(authority.mode)
    }

    #[allow(clippy::too_many_arguments)]
    fn check_call_stmt(
        &mut self,
        span: SpanId,
        cx: Context,
        callee: FnId,
        type_args: &[Ty],
        args: &[Expr],
        dest: Option<&Place>,
        site: SiteId,
    ) {
        self.use_site(site, span);
        let Some(target) = self.index.fns.get(&callee).copied() else {
            self.malformed(span, "call of an unknown function");
            return;
        };
        if target.attrs.broadcast_triggers.is_some() && target.params.is_empty() {
            self.report(
                WfClass::User,
                span,
                "cannot call a broadcast_forall function with 0 arguments directly",
            );
        }
        match target.mode {
            Mode::Spec => self.malformed(span, "a spec function is called as a statement"),
            Mode::Proof => {
                if cx == Context::Exec {
                    self.report(WfClass::User, span, MSG_CALL_PROOF_FROM_EXEC);
                }
            }
            Mode::Exec => {
                if cx.mode() == Mode::Proof {
                    let message = format!("cannot call function `{}` with mode exec", target.name);
                    self.report(WfClass::User, span, message);
                }
            }
        }
        let checks_allowed = cx == Context::Exec && target.mode == Mode::Exec;
        self.check_args(span, target, type_args, args, checks_allowed);
        if let Some(dest) = dest {
            self.check_assignable(dest, span, cx);
            if let (Some(dest_ty), Some(ret_ty)) = (self.place_ty(dest, span), target.ret_ty()) {
                if !self.substituted_type_matches(ret_ty, Some(type_args), &dest_ty) {
                    self.malformed(span, "call destination has the wrong type");
                }
            }
        }
    }

    fn check_args(
        &mut self,
        span: SpanId,
        target: &FnDecl,
        type_args: &[Ty],
        args: &[Expr],
        checks_allowed: bool,
    ) {
        if type_args.len() != target.type_params.len() {
            self.malformed(
                span,
                format!(
                    "`{}` takes {} type arguments, not {}",
                    target.name,
                    target.type_params.len(),
                    type_args.len()
                ),
            );
        }
        for ty in type_args {
            if let Some(problem) = self.index.ty_problem(ty, self.decl.type_params.len()) {
                self.malformed(span, format!("type argument: {problem}"));
            }
        }
        self.discharge_copy(target, type_args, span, false);
        if args.len() != target.params.len() {
            self.malformed(
                span,
                format!(
                    "`{}` takes {} arguments, not {}",
                    target.name,
                    target.params.len(),
                    args.len()
                ),
            );
        }
        for (arg, param) in args.iter().zip(&target.params) {
            let param_mode = target.local(*param).map(|param| param.mode);
            self.check_expr(arg, checks_allowed && param_mode == Some(Mode::Exec));
            if let Some(param_decl) = target.local(*param) {
                if !self.substituted_type_matches(&param_decl.ty, Some(type_args), &arg.ty) {
                    self.malformed(
                        arg.span,
                        format!(
                            "argument for `{}` of `{}` has the wrong type",
                            param_decl.name, target.name
                        ),
                    );
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // Places
    // ------------------------------------------------------------------

    fn project(&mut self, ty: &Ty, projection: Projection, span: SpanId) -> Option<Ty> {
        match (projection, ty) {
            (Projection::Deref, Ty::Ref { inner, .. } | Ty::MutRef(inner)) => {
                Some((**inner).clone())
            }
            (Projection::Field { variant, field }, Ty::Adt(id, args)) => {
                let adt = self.index.adts.get(id).copied();
                let found = adt.and_then(|adt| {
                    if adt.kind != AdtKind::Struct {
                        return None;
                    }
                    adt.field_ty(variant, field, args)
                });
                if found.is_none() {
                    self.malformed(span, "field projection does not name a struct field");
                }
                found
            }
            (Projection::TupleField(index), Ty::Tuple(elems)) => {
                let found = elems.get(index as usize).cloned();
                if found.is_none() {
                    self.malformed(span, "tuple projection out of range");
                }
                found
            }
            _ => {
                self.malformed(
                    span,
                    format!("projection {projection:?} does not apply to {ty:?}"),
                );
                None
            }
        }
    }

    fn place_ty(&mut self, place: &Place, span: SpanId) -> Option<Ty> {
        let Some(root) = self.local(place.local) else {
            self.malformed(
                span,
                format!("place rooted at missing local {}", place.local.0),
            );
            return None;
        };
        let mut ty = root.ty.clone();
        for projection in &place.projections {
            ty = self.project(&ty, *projection, span)?;
        }
        Some(ty)
    }

    /// A read may select an actual enum field just like ExprKind::Field.
    /// This supplies a type, never variant membership or writable storage.
    fn read_place_ty(&mut self, place: &Place, span: SpanId) -> Option<Ty> {
        let Some(root) = self.local(place.local) else {
            self.malformed(
                span,
                format!("read rooted at missing local {}", place.local.0),
            );
            return None;
        };
        let mut ty = root.ty.clone();
        for projection in &place.projections {
            let read_enum = match (projection, &ty) {
                (Projection::Field { variant, field }, Ty::Adt(id, args)) => self
                    .index
                    .adts
                    .get(id)
                    .filter(|adt| adt.kind == AdtKind::Enum)
                    .map(|adt| {
                        if args.len() != adt.type_params.len() {
                            return None;
                        }
                        adt.field_ty(*variant, *field, args)
                    }),
                _ => None,
            };
            ty = match read_enum {
                Some(Some(field)) => field,
                Some(None) => {
                    self.malformed(
                        span,
                        "read projection does not name an actual instantiated enum field",
                    );
                    return None;
                }
                None => self.project(&ty, *projection, span)?,
            };
        }
        Some(ty)
    }

    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------

    fn expect_ty(&mut self, expr: &Expr, want: &Ty, what: &str) {
        // Normal forms are established from one checked program definition
        // table before comparison; no arbitrary RHS is accepted as a match.
        let matches = if self.index.projection_definitions.as_ref().is_some_and(|definitions| !definitions.is_empty()) {
            self.substituted_type_matches(want, None, &expr.ty)
        } else { expr.ty == *want };
        if !matches {
            self.malformed(
                expr.span,
                format!("{what}: expected {want:?}, found {:?}", expr.ty),
            );
        }
    }

    fn check_lit(&mut self, lit: Lit, ty: &Ty, span: SpanId) {
        match (lit, ty) {
            (Lit::Bool(_), Ty::Bool) | (Lit::Unit, Ty::Unit) => {}
            (Lit::Int(value), Ty::Int(range)) => {
                let fits = self.index.architecture.cases().is_ok_and(|widths| {
                    widths.iter().all(|&pw| {
                        let below = range.min(pw).is_some_and(|min| {
                            value.negative && (min >= 0 || value.magnitude > min.unsigned_abs())
                        });
                        let above = range
                            .max(pw)
                            .is_some_and(|max| !value.negative && value.magnitude > max);
                        !below && !above
                    })
                });
                if !fits {
                    self.malformed(span, format!("literal does not fit {range:?}"));
                }
            }
            _ => self.malformed(span, format!("literal {lit:?} does not have type {ty:?}")),
        }
    }

    fn check_expr(&mut self, expr: &Expr, checks_allowed: bool) {
        if let Some(problem) = self.index.ty_problem(&expr.ty, self.decl.type_params.len()) {
            self.malformed(expr.span, problem);
        }
        match &expr.kind {
            ExprKind::Lit(lit) => self.check_lit(*lit, &expr.ty, expr.span),
            ExprKind::IntegerConstant(value) => {
                let expected = match value {
                    crate::IntegerConstant::Minimum(range)
                    | crate::IntegerConstant::Maximum(range) => Ty::Int(*range),
                    crate::IntegerConstant::Bits(_) | crate::IntegerConstant::WordBits => {
                        if expr.ty == Ty::nat() {
                            Ty::nat()
                        } else {
                            Ty::uint(32)
                        }
                    }
                };
                self.expect_ty(expr, &expected, "primitive integer constant");
                if !self
                    .index
                    .architecture
                    .cases()
                    .is_ok_and(|widths| widths.iter().all(|width| value.value(*width).is_some()))
                {
                    self.malformed(expr.span, "an invalid primitive integer constant");
                }
            }
            ExprKind::Read(place) => {
                if let Some(ty) = self.read_place_ty(place, expr.span) {
                    self.expect_ty(expr, &ty, "read");
                }
            }
            ExprKind::Old(place) => {
                if self.local(place.local).map(|local| local.kind) != Some(LocalKind::Param) {
                    self.malformed(expr.span, "old() of something other than a parameter");
                }
                if let Some(ty) = self.read_place_ty(place, expr.span) {
                    self.expect_ty(expr, &ty, "old");
                }
            }
            ExprKind::Unary { op, arg, check } => {
                self.check_expr(arg, checks_allowed);
                self.check_unary(expr, *op, arg, *check, checks_allowed);
            }
            ExprKind::Binary {
                op,
                lhs,
                rhs,
                check,
            } => {
                self.check_expr(lhs, checks_allowed);
                self.check_expr(rhs, checks_allowed);
                self.check_binary(expr, *op, lhs, rhs, *check, checks_allowed);
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                self.check_bool(cond, checks_allowed);
                self.check_expr(then_expr, checks_allowed);
                self.check_expr(else_expr, checks_allowed);
                self.expect_ty(then_expr, &expr.ty, "then branch");
                self.expect_ty(else_expr, &expr.ty, "else branch");
            }
            ExprKind::Let { local, value, body } => {
                match self.local(*local).cloned() {
                    Some(decl) if decl.kind == LocalKind::Bound => {
                        self.check_expr(value, checks_allowed);
                        self.expect_ty(value, &decl.ty, "let value");
                    }
                    _ => self.malformed(expr.span, "spec let of a local that is not a bound local"),
                }
                self.check_expr(body, checks_allowed);
                self.expect_ty(body, &expr.ty, "let body");
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => {
                let Some(target) = self.index.fns.get(callee).copied() else {
                    self.malformed(expr.span, "call of an unknown function");
                    return;
                };
                if target.mode != Mode::Spec {
                    self.malformed(
                        expr.span,
                        format!(
                            "`{}` is called in an expression but is not a spec function",
                            target.name
                        ),
                    );
                }
                self.check_args(expr.span, target, type_args, args, false);
                if let Some(ret_ty) = target.ret_ty() {
                    if !self.substituted_type_matches(ret_ty, Some(type_args), &expr.ty) {
                        self.malformed(expr.span, "call result has the wrong type");
                    }
                }
            }
            ExprKind::Cast { arg, kind } => {
                self.check_expr(arg, checks_allowed);
                match (arg.ty.int_range(), expr.ty.int_range()) {
                    (Some(from), Some(to)) => {
                        if *kind == CastKind::Exact
                            && !self.index.architecture.cases().is_ok_and(|widths| {
                                widths.iter().all(|&width| to.contains(from, width))
                            })
                        {
                            self.malformed(
                                expr.span,
                                format!("exact cast from {from:?} to {to:?} can change the value"),
                            );
                        }
                    }
                    _ => self.malformed(expr.span, "cast between non-integer types"),
                }
            }
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => {
                let declaration = self
                    .index
                    .adts
                    .get(adt)
                    .copied()
                    .and_then(|adt| adt.variants.get(*variant as usize));
                for (index, field) in fields.iter().enumerate() {
                    let mode = declaration
                        .and_then(|variant| variant.fields.get(index))
                        .map(|field| field.mode);
                    self.check_expr(field, checks_allowed && mode == Some(Mode::Exec));
                }
                let args = match &expr.ty {
                    Ty::Adt(id, args) if id == adt => args.clone(),
                    _ => {
                        self.malformed(expr.span, "constructor of another type than its own");
                        Vec::new()
                    }
                };
                let expected: Option<Vec<Ty>> = self
                    .index
                    .adts
                    .get(adt)
                    .filter(|decl| decl.kind != AdtKind::Opaque)
                    .and_then(|decl| decl.variants.get(*variant as usize))
                    .map(|v| v.fields.iter().map(|f| f.ty.subst(&args)).collect());
                match expected {
                    Some(tys) if tys.len() == fields.len() => {
                        for (field, ty) in fields.iter().zip(&tys) {
                            self.expect_ty(field, ty, "constructor field");
                        }
                    }
                    _ => self.malformed(expr.span, "constructor does not match its data type"),
                }
            }
            ExprKind::IsVariant { base, variant } => {
                self.check_expr(base, checks_allowed);
                self.expect_ty(expr, &Ty::Bool, "enum variant test");
                let mut ty = &base.ty;
                while let Ty::Ref {
                    mutable: false,
                    inner,
                } = ty
                {
                    ty = inner;
                }
                let valid = match ty {
                    Ty::Adt(id, _) => self.index.adts.get(id).is_some_and(|decl| {
                        decl.kind == AdtKind::Enum && decl.variants.get(*variant as usize).is_some()
                    }),
                    _ => false,
                };
                if !valid {
                    self.malformed(
                        expr.span,
                        "variant test does not name an actual enum variant",
                    );
                }
            }
            ExprKind::Tuple(elems) => {
                for elem in elems {
                    self.check_expr(elem, checks_allowed);
                }
                let tys = elems.iter().map(|elem| elem.ty.clone()).collect();
                self.expect_ty(expr, &Ty::Tuple(tys), "tuple");
            }
            ExprKind::Field {
                base,
                variant,
                field,
            } => {
                self.check_expr(base, checks_allowed);
                let mut ty = &base.ty;
                while let Ty::Ref {
                    mutable: false,
                    inner,
                } = ty
                {
                    ty = inner;
                }
                let field_ty = match ty {
                    Ty::Adt(id, args)
                        if ty == &base.ty
                            || self
                                .index
                                .adts
                                .get(id)
                                .is_some_and(|adt| adt.kind == AdtKind::Enum) =>
                    {
                        self.index
                            .adts
                            .get(id)
                            .and_then(|decl| decl.field_ty(*variant, *field, args))
                    }
                    _ => None,
                };
                match field_ty {
                    Some(ty) => self.expect_ty(expr, &ty, "field"),
                    None => self.malformed(expr.span, "field of something that has no such field"),
                }
            }
            ExprKind::TupleField { base, index } => {
                self.check_expr(base, checks_allowed);
                match &base.ty {
                    Ty::Tuple(elems) => match elems.get(*index as usize) {
                        Some(ty) => {
                            let ty = ty.clone();
                            self.expect_ty(expr, &ty, "tuple field");
                        }
                        None => self.malformed(expr.span, "tuple field out of range"),
                    },
                    _ => self.malformed(expr.span, "tuple field of a non-tuple"),
                }
            }
            ExprKind::Borrow(inner) => {
                self.check_expr(inner, checks_allowed);
                let want = Ty::Ref {
                    mutable: false,
                    inner: Box::new(inner.ty.clone()),
                };
                self.expect_ty(expr, &want, "borrow");
            }
            ExprKind::MutRefCurrent(reference) | ExprKind::MutRefFuture(reference) => {
                self.check_expr(reference, checks_allowed);
                match &reference.ty {
                    Ty::MutRef(inner) => {
                        self.expect_ty(expr, inner, "mutable-reference projection")
                    }
                    _ => {
                        self.malformed(expr.span, "a mutable-reference projection of another type")
                    }
                }
            }
            ExprKind::MutRefUpdate { reference, value } => {
                self.check_expr(reference, checks_allowed);
                self.check_expr(value, checks_allowed);
                match &reference.ty {
                    Ty::MutRef(inner) => self.expect_ty(value, inner, "mutable-reference update"),
                    _ => self.malformed(expr.span, "a mutable-reference update of another type"),
                }
                self.expect_ty(expr, &reference.ty, "mutable-reference update result");
            }
            ExprKind::HasResolved(value) => {
                self.check_expr(value, checks_allowed);
                self.expect_ty(expr, &Ty::Bool, "resolution predicate");
            }
            ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } => {
                if !self.proof_in_spec {
                    self.malformed(
                        expr.span,
                        "a proof block outside the body of a spec function with a measure",
                    );
                    return;
                }
                if returns(block) {
                    self.malformed(expr.span, "a return inside a proof block in spec code");
                }
                self.expect_ty(expr, &Ty::Unit, "proof block");
                self.proof_in_spec = false;
                self.check_block(block, Context::Proof);
                if let ExprKind::ProofInSpecTail { tail, .. } = &expr.kind {
                    self.check_expr(tail, false);
                    self.expect_ty(tail, &Ty::Unit, "proof block tail");
                }
                self.proof_in_spec = true;
            }
            ExprKind::Quant {
                vars,
                triggers,
                body,
                ..
            } => {
                self.check_binder(expr.span, vars, triggers);
                self.check_bool(body, false);
                self.expect_ty(expr, &Ty::Bool, "quantifier");
            }
            ExprKind::Choose {
                vars,
                triggers,
                cond,
                result,
            } => {
                self.check_binder(expr.span, vars, triggers);
                self.check_bool(cond, false);
                self.check_expr(result, false);
                self.expect_ty(result, &expr.ty, "choice");
            }
            ExprKind::UntriggeredQuant {
                vars,
                trigger_candidates,
                body,
                ..
            } => {
                self.incomplete_binder(expr.span, vars, trigger_candidates);
                self.check_bool(body, false);
                self.expect_ty(expr, &Ty::Bool, "quantifier");
            }
            ExprKind::UntriggeredChoose {
                vars,
                trigger_candidates,
                cond,
                result,
            } => {
                self.incomplete_binder(expr.span, vars, trigger_candidates);
                self.check_bool(cond, false);
                self.check_expr(result, false);
                self.expect_ty(result, &expr.ty, "choice");
            }
        }
    }

    /// The bound locals and triggers of a quantifier or choice: bound
    /// locals, each bound once, and one or more trigger groups, each a
    /// non-empty list of terms that mentions every var.
    fn check_binder(&mut self, span: SpanId, vars: &[(LocalId, Ty)], triggers: &[Vec<Expr>]) {
        self.check_bound_locals(span, vars);
        if triggers.is_empty() {
            self.malformed(span, "a quantifier without triggers");
        }
        for group in triggers {
            if group.is_empty() {
                self.malformed(span, "an empty trigger group");
            }
            for term in group {
                self.check_expr(term, false);
            }
            for (var, _) in vars {
                if !group.iter().any(|term| mentions_local(term, *var)) {
                    self.malformed(span, "a trigger group that does not mention every variable");
                }
            }
        }
    }

    fn incomplete_binder(&mut self, span: SpanId, vars: &[(LocalId, Ty)], candidates: &[Expr]) {
        self.incomplete_binders.push((self.decl.id, span));
        if !self.diagnostics {
            self.malformed(
                span,
                "a source binder whose trigger inference is incomplete",
            );
        }
        self.check_bound_locals(span, vars);
        for term in candidates {
            self.check_expr(term, false);
        }
    }

    fn check_bound_locals(&mut self, span: SpanId, vars: &[(LocalId, Ty)]) {
        if vars.is_empty() {
            self.malformed(span, "a quantifier without variables");
        }
        for (i, (var, ty)) in vars.iter().enumerate() {
            match self.local(*var) {
                Some(decl) if decl.kind == LocalKind::Bound && decl.ty == *ty => {}
                Some(decl) if decl.kind == LocalKind::Bound => {
                    self.malformed(span, "a quantifier variable of another type than its local");
                }
                _ => self.malformed(span, "a quantifier variable that is not a bound local"),
            }
            if vars[..i].iter().any(|(other, _)| other == var) {
                self.malformed(span, "a quantifier variable bound twice");
            }
            if let Some(problem) = self.index.ty_problem(ty, self.decl.type_params.len()) {
                self.malformed(span, problem);
            }
        }
    }

    /// Checked operations need a machine type and exec code; record the site.
    fn check_site(&mut self, expr: &Expr, check: Option<SiteId>, checks_allowed: bool) {
        if let Some(site) = check {
            self.use_site(site, expr.span);
            if !checks_allowed {
                self.malformed(expr.span, "an exec check outside exec code");
            }
            if !expr.ty.int_range().is_some_and(IntRange::is_bounded) {
                self.malformed(
                    expr.span,
                    "an exec check on a type that is not a machine integer",
                );
            }
        }
    }

    fn check_unary(
        &mut self,
        expr: &Expr,
        op: UnOp,
        arg: &Expr,
        check: Option<SiteId>,
        checks_allowed: bool,
    ) {
        self.check_site(expr, check, checks_allowed);
        match op {
            UnOp::Not => {
                let ok = check.is_none()
                    && (arg.ty == Ty::Bool || arg.ty.int_range().is_some_and(IntRange::is_bounded));
                if !ok {
                    self.malformed(
                        expr.span,
                        "`!` needs a bool or a machine integer and no check",
                    );
                }
                self.expect_ty(expr, &arg.ty, "`!` result");
            }
            UnOp::Neg => match check {
                Some(_) => {
                    if !arg.ty.int_range().is_some_and(IntRange::is_signed_machine) {
                        self.malformed(
                            expr.span,
                            "checked negation of an unsigned or math integer",
                        );
                    }
                    self.expect_ty(expr, &arg.ty, "checked negation");
                }
                None => {
                    if !arg.ty.int_range().is_some_and(IntRange::is_math) {
                        self.malformed(expr.span, "spec negation of a machine integer");
                    }
                    self.expect_ty(expr, &Ty::int(), "spec negation");
                }
            },
        }
    }

    fn check_binary(
        &mut self,
        expr: &Expr,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        check: Option<SiteId>,
        checks_allowed: bool,
    ) {
        self.check_site(expr, check, checks_allowed);
        if op.is_arithmetic() {
            match check {
                Some(_) => {
                    self.expect_ty(lhs, &expr.ty, "checked arithmetic operand");
                    self.expect_ty(rhs, &expr.ty, "checked arithmetic operand");
                }
                None => self.check_spec_arith(expr, op, lhs, rhs),
            }
            return;
        }
        if op.is_shift() {
            let lhs_machine = lhs.ty.int_range().is_some_and(IntRange::is_bounded);
            let rhs_machine = rhs.ty.int_range().is_some_and(IntRange::is_bounded);
            if !lhs_machine || !rhs_machine {
                self.malformed(expr.span, "shift operands must be machine integers");
            }
            self.expect_ty(expr, &lhs.ty, "shift result");
            return;
        }
        if check.is_some() {
            self.malformed(expr.span, format!("`{op:?}` cannot carry an exec check"));
        }
        if op.is_comparison() {
            if lhs.ty != rhs.ty {
                self.malformed(expr.span, "comparison of values of different types");
            }
            if !matches!(op, BinOp::Eq | BinOp::Ne) && lhs.ty.int_range().is_none() {
                self.malformed(expr.span, "ordering comparison of non-integers");
            }
            self.expect_ty(expr, &Ty::Bool, "comparison result");
        } else if op.is_logical() {
            self.expect_ty(lhs, &Ty::Bool, "logical operand");
            self.expect_ty(rhs, &Ty::Bool, "logical operand");
            self.expect_ty(expr, &Ty::Bool, "logical result");
        } else if op.is_bitwise() {
            let ok = lhs.ty == rhs.ty
                && (lhs.ty == Ty::Bool || lhs.ty.int_range().is_some_and(IntRange::is_bounded));
            if !ok {
                self.malformed(
                    expr.span,
                    "bitwise operands must be two bools or two machine integers of one type",
                );
            }
            self.expect_ty(expr, &lhs.ty, "bitwise result");
        }
    }

    /// Spec arithmetic: math-typed operands, exact result.
    fn check_spec_arith(&mut self, expr: &Expr, op: BinOp, lhs: &Expr, rhs: &Expr) {
        let lhs_range = lhs.ty.int_range();
        let rhs_range = rhs.ty.int_range();
        if !lhs_range.is_some_and(IntRange::is_math) || !rhs_range.is_some_and(IntRange::is_math) {
            self.malformed(
                expr.span,
                "spec arithmetic on machine integers; cast the operands to int first",
            );
            return;
        }
        let both_nat = lhs_range == Some(IntRange::Nat) && rhs_range == Some(IntRange::Nat);
        let nat_result_ok = both_nat && !matches!(op, BinOp::Sub);
        let ok = expr.ty == Ty::int() || (expr.ty == Ty::nat() && nat_result_ok);
        if !ok {
            self.malformed(
                expr.span,
                format!("spec `{op:?}` cannot have type {:?}", expr.ty),
            );
        }
    }
}

/// The span of the first assignment anywhere in `block`, if any.
fn first_assignment(block: &Block) -> Option<SpanId> {
    block.stmts.iter().find_map(|stmt| match &stmt.kind {
        StmtKind::Assign { .. } | StmtKind::AssignSpec { .. } => Some(stmt.span),
        StmtKind::If {
            then_block,
            else_block,
            ..
        }
        | StmtKind::IfSpec {
            then_block,
            else_block,
            ..
        } => first_assignment(then_block).or_else(|| first_assignment(else_block)),
        StmtKind::Ghost(inner)
        | StmtKind::Block(inner)
        | StmtKind::GhostTail { block: inner, .. } => first_assignment(inner),
        StmtKind::Loop(lp) => lp
            .cond
            .as_ref()
            .and_then(|cond| first_assignment(&cond.block))
            .or_else(|| first_assignment(&lp.body)),
        _ => None,
    })
}

/// Does `expr` read `local` (currently or through `Old`)?
#[must_use]
pub fn mentions_local(expr: &Expr, local: LocalId) -> bool {
    expr.any(&|e| match &e.kind {
        ExprKind::Read(place) | ExprKind::Old(place) => place.local == local,
        ExprKind::Let { local: bound, .. } => *bound == local,
        ExprKind::Quant { vars, .. }
        | ExprKind::Choose { vars, .. }
        | ExprKind::UntriggeredQuant { vars, .. }
        | ExprKind::UntriggeredChoose { vars, .. } => vars.iter().any(|(var, _)| *var == local),
        _ => false,
    })
}

/// Does `block` hold a `return`, at any depth?
fn returns(block: &Block) -> bool {
    block.stmts.iter().any(|stmt| match &stmt.kind {
        StmtKind::Return { .. } => true,
        StmtKind::If {
            then_block,
            else_block,
            ..
        }
        | StmtKind::IfSpec {
            then_block,
            else_block,
            ..
        } => returns(then_block) || returns(else_block),
        StmtKind::Ghost(inner)
        | StmtKind::Block(inner)
        | StmtKind::GhostTail { block: inner, .. } => returns(inner),
        StmtKind::Loop(lp) => {
            lp.cond.as_ref().is_some_and(|c| returns(&c.block)) || returns(&lp.body)
        }
        _ => false,
    })
}
