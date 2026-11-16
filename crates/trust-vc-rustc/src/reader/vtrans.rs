//! Whether Verus can translate a type, and the bounds of the items it
//! translates.
//!
//! Verus turns every type it meets into a VIR type
//! (`rust_to_vir_base.rs`, `mid_ty_to_vir`): the type of each expression it
//! converts, each type argument of a call (`fn_call_to_vir.rs`,
//! `mk_typ_args`), each type in a bound (`process_predicate_bounds`), the
//! self type and trait arguments of an implementation. For a datatype it
//! also collects the implementations that satisfy the datatype's bounds
//! (`get_impl_paths`), and it does the same for the bounds of a function it
//! calls. Each step rejects some types: a function pointer, `&mut` outside
//! the places that allow it, a constant argument that is not an integer or
//! a `bool`, a trait method item that resolves to a builtin implementation,
//! a bound met by a builtin implementation it does not recognize, or by the
//! `Deref` of `Ghost` and `Tracked`.
//!
//! [`Cx::verus_ty_problem`] and its relatives follow those steps and name
//! what Verus rejects. Where the reader cannot tell (a selection it cannot
//! repeat, a kind of type it does not follow), they name that too: the
//! caller refuses either way, so a type is accepted only when Verus is known
//! to translate it.
//!
//! A type Verus translates can still fail its well-formedness check, which
//! looks up every datatype, function item and projected trait in the crate's
//! VIR; [`Cx::verus_wf_problem`] follows that check.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::traits::{BuiltinImplSource, ImplSource};
use rustc_middle::ty::{self, GenericArg, GenericArgKind, Ty, TypeVisitableExt, Upcast};
use rustc_span::sym;

use super::{Cx, Refusal};
use crate::verus_items::VerusItem;

/// Upper bound on the bounds one check follows, as Verus bounds its own
/// worklist.
const MAX_BOUNDS: usize = 10_000;

// Internally, the first problem wins. A native query failure occupies that
// position too: Option::or_else/find_map must never skip it. Public probes
// transpose this to an explicit fallible result before leaving the module.
type Problem = Option<Result<String, Refusal>>;

impl<'tcx> Cx<'tcx> {
    /// What Verus's type translation rejects in `ty`, or what the reader
    /// cannot decide about it; `Ok(None)` when Verus translates it. A native
    /// normalization failure is `Err`, never a purported Verus rule. `env` is
    /// the item whose bounds are in scope (Verus's `param_env_src`).
    pub(crate) fn verus_ty_problem(
        &self,
        ty: Ty<'tcx>,
        env: DefId,
    ) -> Result<Option<String>, Refusal> {
        self.ty_problem(ty, env, false).transpose()
    }

    /// [`Self::verus_ty_problem`] where Verus allows `&mut` (the type of a
    /// parameter, for example), as the reader's own types do.
    pub(crate) fn verus_ty_problem_allowing_mut(
        &self,
        ty: Ty<'tcx>,
        env: DefId,
    ) -> Result<Option<String>, Refusal> {
        self.ty_problem(ty, env, true).transpose()
    }

    fn ty_problem(&self, ty: Ty<'tcx>, env: DefId, allow_mut: bool) -> Problem {
        let tcx = self.tcx;
        let problem = |what: &str| Some(Ok(format!("{what} `{ty}`")));
        match ty.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Never
            | ty::Str
            | ty::Param(_) => None,
            ty::Ref(_, inner, mutability) => {
                if mutability.is_mut() && !allow_mut && !self.opts.new_mut_ref {
                    return problem("the `&mut` type");
                }
                self.ty_problem(*inner, env, allow_mut)
            }
            ty::Tuple(elems) => elems
                .iter()
                .find_map(|t| self.ty_problem(t, env, allow_mut)),
            ty::Slice(elem) | ty::RawPtr(elem, _) => self.ty_problem(*elem, env, allow_mut),
            ty::Array(elem, len) => self
                .ty_problem(*elem, env, allow_mut)
                .or_else(|| self.verus_const_problem(*len, env).map(Ok)),
            ty::Adt(adt, args) => {
                let did = adt.did();
                let item = self.verus_item(did);
                if matches!(item, Some(VerusItem::Int | VerusItem::Nat)) {
                    return None;
                }
                if let Some(problem) = args
                    .iter()
                    .find_map(|a| self.arg_problem(a, env, allow_mut))
                {
                    return Some(problem);
                }
                let types = args.types().count();
                let decorated = (Some(did) == tcx.lang_items().owned_box() && types == 2)
                    || (types >= 1
                        && (matches!(item, Some(VerusItem::Ghost | VerusItem::Tracked))
                            || tcx.is_diagnostic_item(sym::Rc, did)
                            || tcx.is_diagnostic_item(sym::Arc, did)));
                if decorated {
                    return None;
                }
                if item == Some(VerusItem::FnSpec) {
                    return match args.types().next().map(|t| t.kind()) {
                        Some(ty::Tuple(_)) => None,
                        _ => problem("a `spec_fn` type whose parameters are not a tuple"),
                    };
                }
                self.bounds_problem(did, *args, env)
            }
            ty::Closure(_, args) => {
                let sig = args.as_closure().sig().skip_binder();
                sig.inputs()
                    .iter()
                    .chain([&sig.output()])
                    .find_map(|t| self.ty_problem(*t, env, allow_mut))
            }
            ty::FnDef(def_id, args) => {
                let Some(args) = args.no_bound_vars() else {
                    return problem("a function item with higher-ranked generic arguments");
                };
                if tcx.trait_of_assoc(*def_id).is_some() {
                    match self.select_trait_item(*def_id, args, env) {
                        Ok(Some(ImplSource::UserDefined(_) | ImplSource::Param(_))) => {}
                        Ok(Some(ImplSource::Builtin(..))) => {
                            return problem("a function item that resolves to a builtin instance")
                        }
                        Ok(None) => {
                            return problem("a function item whose implementation is not known")
                        }
                        Err(problem) => return Some(Err(problem)),
                    }
                }
                args.iter().find_map(|a| self.arg_problem(a, env, false))
            }
            // Verus translates a `dyn` type with one trait, and checks the
            // trait's dyn compatibility by rules of its own
            // (`vir/src/traits.rs`), which the reader does not follow.
            ty::Dynamic(..) => problem("the `dyn` type"),
            ty::Alias(_, alias) => match alias.kind {
                ty::AliasTyKind::Projection { .. } => {
                    let typing_env = ty::TypingEnv::non_body_analysis(tcx, env);
                    if let Ok(normal) =
                        tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new(ty))
                    {
                        if normal != ty {
                            return self.ty_problem(normal, env, allow_mut);
                        }
                    }
                    if alias.args.types().next().is_none() {
                        return problem("a projection without a self type");
                    }
                    alias
                        .args
                        .iter()
                        .find_map(|a| self.arg_problem(a, env, false))
                }
                ty::AliasTyKind::Opaque { .. } => alias
                    .args
                    .iter()
                    .find_map(|a| self.arg_problem(a, env, false)),
                _ => problem("the alias type"),
            },
            _ => problem("the type"),
        }
    }

    /// [`Self::verus_ty_problem`] for a generic argument: a type, a lifetime
    /// (ignored) or a constant.
    pub(crate) fn verus_arg_problem(
        &self,
        arg: GenericArg<'tcx>,
        env: DefId,
    ) -> Result<Option<String>, Refusal> {
        self.arg_problem(arg, env, false).transpose()
    }

    fn arg_problem(&self, arg: GenericArg<'tcx>, env: DefId, allow_mut: bool) -> Problem {
        match arg.kind() {
            GenericArgKind::Type(t) => self.ty_problem(t, env, allow_mut),
            GenericArgKind::Lifetime(_) => None,
            GenericArgKind::Const(c) => self.verus_const_problem(c, env).map(Ok),
        }
    }

    /// A constant argument Verus does not translate
    /// (`mid_ty_const_to_vir`): one that is neither a constant parameter
    /// nor an integer or `bool` value.
    fn verus_const_problem(&self, c: ty::Const<'tcx>, env: DefId) -> Option<String> {
        let tcx = self.tcx;
        let c = match c.kind() {
            ty::ConstKind::Alias(..) => {
                let typing_env = ty::TypingEnv::post_analysis(tcx, env);
                match tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new(c)) {
                    Ok(c) => c,
                    Err(_) => return Some(format!("the constant argument `{c}`")),
                }
            }
            _ => c,
        };
        match c.kind() {
            ty::ConstKind::Param(_) => None,
            ty::ConstKind::Value(value)
                if value.try_to_leaf().is_some()
                    && matches!(value.ty.kind(), ty::Int(_) | ty::Uint(_) | ty::Bool) =>
            {
                None
            }
            _ => Some(format!("the constant argument `{c}`")),
        }
    }

    /// What Verus rejects while it collects the implementations that meet
    /// the bounds of `def_id` (and of its parents) at `args`
    /// (`get_impl_paths`), and the bounds of those implementations in turn.
    pub(crate) fn verus_bounds_problem(
        &self,
        def_id: DefId,
        args: ty::GenericArgs<'tcx>,
        env: DefId,
    ) -> Result<Option<String>, Refusal> {
        self.bounds_problem(def_id, args, env).transpose()
    }

    fn bounds_problem(&self, def_id: DefId, args: ty::GenericArgs<'tcx>, env: DefId) -> Problem {
        let tcx = self.tcx;
        let mut work: Vec<ty::Clause<'tcx>> = tcx
            .clauses_of(def_id)
            .instantiate(tcx, args)
            .clauses
            .into_iter()
            .map(|clause| clause.skip_normalization())
            .collect();
        let typing_env = ty::TypingEnv::non_body_analysis(tcx, env);
        let lang = tcx.lang_items();
        let mut index = 0;
        while index < work.len() {
            if index >= MAX_BOUNDS {
                return Some(Ok(format!(
                    "more than {MAX_BOUNDS} bounds behind `{}`",
                    tcx.def_path_str(def_id)
                )));
            }
            let clause = work[index];
            index += 1;
            let ty::ClauseKind::Trait(pred) =
                tcx.instantiate_bound_regions_with_erased(clause.kind())
            else {
                continue;
            };
            let trait_ref = match self.normalized(typing_env, pred.trait_ref, env) {
                Ok(reference) => reference,
                Err(problem) => return Some(Err(problem)),
            };
            let candidate = tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref));
            let unrecognized = || {
                Some(Ok(format!(
                    "the bound `{trait_ref}`, met by a builtin impl"
                )))
            };
            match candidate {
                Ok(ImplSource::UserDefined(data)) => {
                    if self.is_ghost_deref_impl(data.impl_def_id) {
                        return Some(Ok(format!(
                            "the bound `{trait_ref}`, met by the `Deref` of `Ghost` or `Tracked`"
                        )));
                    }
                    for nested in tcx
                        .clauses_of(data.impl_def_id)
                        .instantiate(tcx, data.args)
                        .clauses
                    {
                        let nested = nested.skip_normalization();
                        if !work.contains(&nested) {
                            work.push(nested);
                        }
                    }
                }
                Ok(ImplSource::Param(_) | ImplSource::Builtin(BuiltinImplSource::Object(_), _)) => {
                }
                Ok(ImplSource::Builtin(..)) => {
                    if pred.polarity != ty::ClausePolarity::Positive {
                        return unrecognized();
                    }
                    let id = trait_ref.def_id;
                    let self_ty = trait_ref.self_ty();
                    if [lang.fn_trait(), lang.fn_mut_trait(), lang.fn_once_trait()]
                        .contains(&Some(id))
                    {
                        if let ty::FnDef(f, f_args) = self_ty.kind() {
                            let Some(f_args) = f_args.no_bound_vars() else {
                                return Some(Ok(format!(
                                    "the bound `{trait_ref}` on a function item with higher-ranked generic arguments"
                                )));
                            };
                            for nested in tcx.clauses_of(*f).instantiate(tcx, f_args).clauses {
                                let nested = nested.skip_normalization();
                                if !work.contains(&nested) {
                                    work.push(nested);
                                }
                            }
                        }
                    } else if [
                        lang.sized_trait(),
                        lang.meta_sized_trait(),
                        lang.copy_trait(),
                        lang.tuple_trait(),
                        lang.pointee_trait(),
                        lang.sync_trait(),
                        lang.destruct_trait(),
                    ]
                    .contains(&Some(id))
                        || tcx.is_diagnostic_item(sym::Send, id)
                        || tcx
                            .get_diagnostic_name(id)
                            .is_some_and(|name| name.as_str() == "Any")
                    {
                    } else if Some(id) == lang.clone_trait() {
                        let ty::Tuple(elems) = self_ty.kind() else {
                            return unrecognized();
                        };
                        for elem in elems.iter() {
                            let nested: ty::Clause<'tcx> =
                                ty::Binder::dummy(ty::ClauseKind::Trait(ty::TraitClause {
                                    trait_ref: ty::TraitRef::new(tcx, id, [elem]),
                                    polarity: ty::ClausePolarity::Positive,
                                }))
                                .upcast(tcx);
                            work.push(nested);
                        }
                    } else {
                        return unrecognized();
                    }
                }
                // Verus goes on when the selection fails.
                Err(_) => {}
            }
        }
        None
    }

    /// The implementation source of the trait of the trait item `def_id` at
    /// `args`, as Verus resolves a function item's type (`resolve_traits.rs`,
    /// `resolve_trait_item`). Only a native selection failure is `Ok(None)`;
    /// an unavailable normalization/binder is an explicit refusal.
    fn select_trait_item(
        &self,
        def_id: DefId,
        args: ty::GenericArgs<'tcx>,
        env: DefId,
    ) -> Result<Option<&'tcx ImplSource<'tcx, ()>>, Refusal> {
        let tcx = self.tcx;
        let Some(trait_id) = tcx.trait_of_assoc(def_id) else {
            return Ok(None);
        };
        let typing_env = ty::TypingEnv::post_analysis(tcx, env);
        let args = tcx.erase_and_anonymize_regions(args);
        let trait_ref = ty::TraitRef::new(
            tcx,
            trait_id,
            args.iter().take(tcx.generics_of(trait_id).count()),
        );
        let trait_ref = self.normalized(typing_env, trait_ref, env)?;
        Ok(tcx
            .codegen_select_candidate(typing_env.as_query_input(trait_ref))
            .ok())
    }

    /// A native selection key, fully normalized in this exact environment.
    /// Neither an unsupported binder nor failed normalization is "no impl".
    fn normalized(
        &self,
        typing_env: ty::TypingEnv<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        origin: DefId,
    ) -> Result<ty::TraitRef<'tcx>, Refusal> {
        let tcx = self.tcx;
        let erased = tcx.erase_and_anonymize_regions(trait_ref);
        let unsupported = || {
            Refusal::new(
                "trait-normalization",
                "a trait selection key with unsupported bound, opaque, inference or error types",
                tcx.def_span(origin),
            )
        };
        if !selectable(erased) {
            return Err(unsupported());
        }
        let normalized = tcx
            .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new(erased))
            .map_err(|problem| {
                Refusal::new(
                    "trait-normalization",
                    format!("cannot normalize the native trait selection key: {problem:?}"),
                    tcx.def_span(origin),
                )
            })?;
        if !selectable(normalized) {
            return Err(unsupported());
        }
        Ok(normalized)
    }

    /// The builtin `Deref` or `DerefMut` implementation of `Ghost` or
    /// `Tracked` (`err_for_builtin_tracked_ghost_deref`).
    fn is_ghost_deref_impl(&self, impl_id: DefId) -> bool {
        let tcx = self.tcx;
        if !matches!(tcx.def_kind(impl_id), DefKind::Impl { of_trait: true }) {
            return false;
        }
        let trait_ref = tcx
            .impl_trait_ref(impl_id)
            .instantiate_identity()
            .skip_normalization();
        let lang = tcx.lang_items();
        if ![lang.deref_trait(), lang.deref_mut_trait()].contains(&Some(trait_ref.def_id)) {
            return false;
        }
        if tcx.impl_polarity(impl_id) == ty::ImplPolarity::Negative {
            return false;
        }
        match trait_ref.self_ty().kind() {
            ty::Adt(adt, _) => matches!(
                self.verus_item(adt.did()),
                Some(VerusItem::Ghost | VerusItem::Tracked)
            ),
            _ => false,
        }
    }

    /// What Verus's well-formedness check rejects in `ty`
    /// (`vir/src/well_formed.rs`, `check_one_typ` on every type nested in
    /// the VIR type `mid_ty_to_vir` builds): a datatype that is not in the
    /// crate's VIR (`check_path_and_get_datatype`: "is not supported", or
    /// "cannot use type ... which is ignored"), a function item of a
    /// function that is not (`check_function_access`), and a projection of
    /// a trait that is not. `Box`, `Rc` and `Arc` carry their allocator,
    /// `alloc::alloc::Global` unless written otherwise, which is checked
    /// too. Verus runs the check over the types of a function's signature
    /// and body, the type arguments of its calls among them, and over the
    /// self type and trait arguments of each trait implementation.
    ///
    /// The reader refuses programs that use vstd, so the crate's VIR holds
    /// only the datatypes and traits of this crate that Verus reads
    /// ([`super::is_verus_datatype`], [`super::is_verus_trait`]): an std
    /// type such as `Option` is not among them. `Ok(None)` when the check
    /// accepts `ty`; an unsupported type is a problem and a failed native
    /// selection-key normalization is `Err`.
    pub(crate) fn verus_wf_problem(
        &self,
        ty: Ty<'tcx>,
        env: DefId,
    ) -> Result<Option<String>, Refusal> {
        self.wf_problem(ty, env).transpose()
    }

    fn wf_problem(&self, ty: Ty<'tcx>, env: DefId) -> Problem {
        let tcx = self.tcx;
        let problem = |what: &str, why: &str| Some(Ok(format!("{what} `{ty}`, {why},")));
        let types =
            |args: ty::GenericArgs<'tcx>| args.types().find_map(|t| self.wf_problem(t, env));
        match ty.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Never
            | ty::Str
            | ty::Param(_) => None,
            ty::Ref(_, inner, _)
            | ty::Slice(inner)
            | ty::RawPtr(inner, _)
            | ty::Array(inner, _) => self.wf_problem(*inner, env),
            ty::Tuple(elems) => elems.iter().find_map(|t| self.wf_problem(t, env)),
            ty::Adt(adt, args) => {
                let did = adt.did();
                let item = self.verus_item(did);
                if matches!(item, Some(VerusItem::Int | VerusItem::Nat)) {
                    return None;
                }
                if let Some(problem) = types(*args) {
                    return Some(problem);
                }
                let count = args.types().count();
                let builtin = (Some(did) == tcx.lang_items().owned_box() && count == 2)
                    || (count >= 1
                        && (matches!(
                            item,
                            Some(VerusItem::Ghost | VerusItem::Tracked | VerusItem::FnSpec)
                        ) || tcx.is_diagnostic_item(sym::Rc, did)
                            || tcx.is_diagnostic_item(sym::Arc, did)));
                if builtin || super::is_verus_datatype(self, did) {
                    None
                } else {
                    problem("the datatype", "which Verus does not declare")
                }
            }
            ty::Closure(_, args) => {
                let sig = args.as_closure().sig().skip_binder();
                sig.inputs()
                    .iter()
                    .chain([&sig.output()])
                    .find_map(|t| self.wf_problem(*t, env))
            }
            ty::FnDef(def_id, args) => {
                let Some(args) = args.no_bound_vars() else {
                    return problem(
                        "the function item",
                        "whose higher-ranked generic arguments the reader does not follow",
                    );
                };
                if !self.fns.contains_key(def_id) {
                    return problem("the function item", "whose function Verus does not declare");
                }
                // The implementation a trait method item resolves to is
                // checked too.
                if tcx.trait_of_assoc(*def_id).is_some() {
                    let selection = match self.select_trait_item(*def_id, args, env) {
                        Ok(selection) => selection,
                        Err(problem) => return Some(Err(problem)),
                    };
                    if let Some(ImplSource::UserDefined(data)) = selection {
                        if let Some(method) =
                            tcx.impl_item_implementor_ids(data.impl_def_id).get(def_id)
                        {
                            if !self.fns.contains_key(method) {
                                return problem(
                                    "the function item",
                                    "whose implementation Verus does not declare",
                                );
                            }
                        }
                    }
                }
                types(args)
            }
            ty::Alias(_, alias) => match alias.kind {
                ty::AliasTyKind::Projection { def_id } => {
                    let def_id: DefId = def_id;
                    let typing_env = ty::TypingEnv::non_body_analysis(tcx, env);
                    if let Ok(normal) =
                        tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new(ty))
                    {
                        if normal != ty {
                            return self.wf_problem(normal, env);
                        }
                    }
                    let trait_id = tcx.parent(def_id);
                    if !super::is_verus_trait(tcx, trait_id, self.opts.no_external_by_default) {
                        return problem("the projection", "whose trait Verus does not declare");
                    }
                    types(alias.args)
                }
                ty::AliasTyKind::Opaque { .. } => types(alias.args),
                _ => problem("the alias type", "which the reader does not follow"),
            },
            _ => problem("the type", "which the reader does not follow"),
        }
    }

    /// What Verus rejects in the types of the bounds written on `def_id`
    /// (`process_predicate_bounds`, from `check_generics_bounds`), with the
    /// span of the bound. The bounds of its parent items are checked with
    /// those items.
    pub(crate) fn verus_where_problem(
        &self,
        def_id: DefId,
    ) -> Result<Option<(String, rustc_span::Span)>, Refusal> {
        let tcx = self.tcx;
        for (clause, span) in tcx.clauses_of(def_id).clauses {
            let problem = match clause.kind().skip_binder() {
                ty::ClauseKind::RegionOutlives(_) | ty::ClauseKind::TypeOutlives(_) => None,
                ty::ClauseKind::Trait(pred) => {
                    if pred.polarity == ty::ClausePolarity::Positive {
                        pred.trait_ref
                            .args
                            .iter()
                            .find_map(|a| self.arg_problem(a, def_id, false))
                    } else {
                        Some(Ok(format!("the negative bound `{pred}`")))
                    }
                }
                ty::ClauseKind::Projection(pred) => match pred.term.as_type() {
                    Some(t) => self.ty_problem(t, def_id, false).or_else(|| {
                        pred.projection_term
                            .args
                            .iter()
                            .find_map(|a| self.arg_problem(a, def_id, false))
                    }),
                    None => Some(Ok(format!("the bound `{pred}`"))),
                },
                ty::ClauseKind::ConstArgHasType(c, t) => self
                    .verus_const_problem(c, def_id)
                    .map(Ok)
                    .or_else(|| self.ty_problem(t, def_id, false)),
                _ => Some(Ok(format!("the bound `{clause}`"))),
            };
            // Verus does not run its well-formedness check over bounds. A
            // bound with a type the check would reject makes Verus panic
            // where it encodes the bound (`sst_to_air.rs`,
            // `recursive_types.rs`), and passes where it does not; the
            // reader refuses every such bound.
            let problem = problem.or_else(|| match clause.kind().skip_binder() {
                ty::ClauseKind::Trait(pred) => pred
                    .trait_ref
                    .args
                    .types()
                    .find_map(|t| self.wf_problem(t, def_id)),
                ty::ClauseKind::Projection(pred) => pred
                    .projection_term
                    .args
                    .types()
                    .chain(pred.term.as_type())
                    .find_map(|t| self.wf_problem(t, def_id)),
                ty::ClauseKind::ConstArgHasType(_, t) => self.wf_problem(t, def_id),
                _ => None,
            });
            if let Some(problem) = problem {
                return problem.map(|detail| Some((detail, *span)));
            }
        }
        Ok(None)
    }
}

/// A trait reference the reader hands to rustc's selection: no escaping
/// bound variables, opaque or inference types, or errors, any of which
/// rustc's codegen selection does not expect.
fn selectable(trait_ref: ty::TraitRef<'_>) -> bool {
    !(trait_ref.has_escaping_bound_vars()
        || trait_ref.has_opaque_types()
        || trait_ref.has_infer()
        || trait_ref.has_placeholders()
        || trait_ref.references_error())
}
