//! Exact native call/impl selection in the original caller's generic context.

use super::*;

pub(super) struct Call<'tcx> {
    span: AuthoredSpan,
    declared: DefId,
    declared_args: ty::GenericArgsRef<'tcx>,
    target: DefId,
    target_args: ty::GenericArgsRef<'tcx>,
    selected_impl: Option<DefId>,
    declaration_clauses: Vec<ClauseInput<'tcx>>,
    target_clauses: Vec<ClauseInput<'tcx>>,
    impl_clauses: Vec<ClauseInput<'tcx>>,
    intrinsic: Option<intrinsics::Kind>,
}

impl Call<'_> {
    pub(super) fn target(&self) -> DefId {
        self.target
    }
    pub(super) fn is_intrinsic(&self) -> bool {
        self.intrinsic.is_some()
    }
    pub(super) fn trait_declaration(&self) -> Option<DefId> {
        self.selected_impl.map(|_| self.declared)
    }
    pub(super) fn observation(&self, tcx: TyCtxt<'_>) -> Value {
        json!({"declared": key_json(declaration_native::key(tcx, self.declared)),
            "selected": key_json(declaration_native::key(tcx, self.target)),
            "selected_impl": self.selected_impl.map(|def| key_json(declaration_native::key(tcx, def))),
            "declared_argument_count": self.declared_args.len(),
            "selected_argument_count": self.target_args.len(),
            "declaration_clauses": self.declaration_clauses.len(),
            "selected_clauses": self.target_clauses.len(), "impl_clauses": self.impl_clauses.len(),
            "source_file": self.span.relative_file, "source_bytes": self.span.bytes,
            "fresh_intrinsic": self.intrinsic.map(|kind| format!("{kind:?}")),
            "ghost_redirect_applied": false})
    }
}

pub(super) struct ClauseInput<'tcx> {
    pub(super) scope: DefId,
    pub(super) clause: ty::Clause<'tcx>,
    pub(super) span: Span,
}

pub(super) fn clauses<'tcx>(
    tcx: TyCtxt<'tcx>,
    definition: DefId,
    args: ty::GenericArgsRef<'tcx>,
    env: ty::TypingEnv<'tcx>,
) -> Result<Vec<ClauseInput<'tcx>>, String> {
    let mut result = Vec::new();
    let mut current = Some(definition);
    let mut scopes = HashSet::new();
    while let Some(scope) = current {
        if !scopes.insert(scope) || scopes.len() > 64 {
            return Err("Spec graph native clause scope chain is cyclic or too deep".into());
        }
        let native = tcx.clauses_of(scope);
        if native.parent != tcx.generics_of(scope).parent
            || result.len().saturating_add(native.clauses.len()) > 4096
        {
            return Err("Spec graph clause parent or bound is inconsistent".into());
        }
        for (clause, span) in native.instantiate_own(tcx, args) {
            result.push(ClauseInput {
                scope,
                span,
                clause: tcx
                    .try_normalize_erasing_regions(env, clause)
                    .map_err(|_| "an actual substituted Spec graph clause cannot be normalized")?,
            });
        }
        current = native.parent;
    }
    Ok(result)
}

pub(super) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    span: Span,
    declared: DefId,
    original_args: ty::GenericArgsRef<'tcx>,
    scope: &Intrinsics<'_, 'tcx>,
) -> Result<Call<'tcx>, String> {
    scope.current(tcx)?;
    let env = ty::TypingEnv::non_body_analysis(tcx, owner.to_def_id());
    if original_args.len() != tcx.generics_of(declared).count() || original_args.len() > 256 {
        return Err("a Spec graph call has a different native generic arity".into());
    }
    let args = tcx
        .try_normalize_erasing_regions(env, ty::Unnormalized::new(original_args))
        .map_err(|_| "actual Spec graph call arguments cannot be normalized")?;
    // These are actual native values, not a Debug-text digest or an erased
    // ordinal vector. The future body producer must retain every argument.
    if args
        .iter()
        .any(|arg| !matches!(arg.kind(), ty::GenericArgKind::Type(_)))
    {
        return Err("Spec graph lifetime/const substitutions need a typed codec".into());
    }
    let intrinsic = scope.kind(declared);
    let (target, target_args, selected_impl, impl_clauses) = if let Some(trait_id) =
        tcx.trait_of_assoc(declared)
    {
        let count = tcx.generics_of(trait_id).count();
        if args.len() < count {
            return Err("a Spec graph trait argument prefix is incomplete".into());
        }
        let requested = ty::TraitRef::new(tcx, trait_id, args.iter().take(count));
        let Ok(rustc_middle::traits::ImplSource::UserDefined(selection)) =
            tcx.codegen_select_candidate(env.as_query_input(requested))
        else {
            return Err("a Spec graph trait call has no exact user impl selection".into());
        };
        let actual = tcx
            .try_normalize_erasing_regions(
                env,
                tcx.impl_trait_ref(selection.impl_def_id)
                    .instantiate(tcx, selection.args),
            )
            .map_err(|_| "the selected Spec graph impl trait reference cannot be normalized")?;
        if actual != requested {
            return Err("the selected impl has another native trait substitution".into());
        }
        let mut members = tcx
            .associated_items(selection.impl_def_id)
            .in_definition_order()
            .filter(|member| member.trait_item_def_id() == Some(declared));
        let target = members
            .next()
            .map(|member| member.def_id)
            .ok_or("an inherited/default trait body needs its own complete Spec graph")?;
        if members.next().is_some()
            || tcx.def_kind(target) != DefKind::AssocFn
            || tcx.trait_impl_of_assoc(target) != Some(selection.impl_def_id)
        {
            return Err("the selected Spec graph impl member is not unique and exact".into());
        }
        let selected_args = args.rebase_onto(tcx, trait_id, selection.args);
        if selected_args.len() != tcx.generics_of(target).count()
            || selected_args
                .iter()
                .any(|arg| !matches!(arg.kind(), ty::GenericArgKind::Type(_)))
        {
            return Err("the selected Spec graph member has another generic arity".into());
        }
        let declaration_signature = tcx
            .try_normalize_erasing_regions(env, tcx.fn_sig(declared).instantiate(tcx, args))
            .map_err(|_| "the substituted trait declaration signature cannot be normalized")?;
        let selected_signature = tcx
            .try_normalize_erasing_regions(env, tcx.fn_sig(target).instantiate(tcx, selected_args))
            .map_err(|_| "the substituted impl member signature cannot be normalized")?;
        if declaration_signature != selected_signature {
            return Err(
                "the actual selected trait/member signatures differ after substitution".into(),
            );
        }
        (
            target,
            selected_args,
            Some(selection.impl_def_id),
            clauses(tcx, selection.impl_def_id, selection.args, env)?,
        )
    } else {
        (declared, args, None, Vec::new())
    };
    Ok(Call {
        span: declaration_native::span(tcx, &scope.inputs.sources, span)?,
        declared,
        declared_args: args,
        target,
        target_args,
        selected_impl,
        declaration_clauses: clauses(tcx, declared, args, env)?,
        target_clauses: clauses(tcx, target, target_args, env)?,
        impl_clauses,
        intrinsic,
    })
}
