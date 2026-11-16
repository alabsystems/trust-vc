//! Original inputs for one inherent inline wrapper and bodyless dependencies.
//!
//! This capture deliberately grants no signature, clause or equation. The
//! separate source reader must lower and strictly check the complete fragment.

use super::*;
use crate::reader::declaration_headers::{self, CheckedHeaders};
use trust_vc_vcir::{AdtKind, IntRange};

#[path = "source_family.rs"]
mod source_family;
pub(in crate::reader::declaration_staging::spec_graph::definitions) use source_family::map_function as map_source_function;
pub(in crate::reader::declaration_staging) use source_family::OwnedSourceFamily;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Bodyless,
    InlineRoot,
}

pub(in crate::reader::declaration_staging) struct LiveForwardingGraph<'scope, 'tcx> {
    original: LiveGraph<'scope, 'tcx>,
    headers: BTreeMap<NativeKey, CheckedHeaders<'tcx>>,
    kinds: BTreeMap<NativeKey, Kind>,
    recommends: DefId,
}

/// Completed source semantics still borrowed from the actual native graph
/// and carrier scope. This has no import or native-signature constructor.
pub(in crate::reader::declaration_staging) struct CheckedSourceRead<'read, 'scope, 'tcx> {
    graph: &'read LiveForwardingGraph<'scope, 'tcx>,
    nominal: &'read SourceNominals<'read, 'tcx>,
    read: crate::reader::CrateRead,
    definitions: CheckedSpecDefinitions,
    forwarding: FnId,
    index: FnId,
    length: FnId,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::reader) enum SourceHeaderKind {
    Recommendations,
    InlineForwarder,
}

/// This requirement cannot authorize a signature on its own. The retained
/// native function must keep its exact semantic packet through client joining.
pub(in crate::reader) struct OwnedSourceHeader {
    root: NativeKey,
    owner: NativeKey,
    counterpart: NativeKey,
    source: SourceIdentity,
    kind: SourceHeaderKind,
}

impl OwnedSourceHeader {
    pub(in crate::reader) fn recommendations_only(&self) -> bool {
        self.kind == SourceHeaderKind::Recommendations
    }
}

/// Only a complete, strictly checked original read can mint this borrowed
/// function evidence. The factory must still perform every ordinary native
/// origin, type, mode, source and counterpart check.
pub(in crate::reader) struct CheckedSourceFunction<'facts, 'tcx> {
    tcx: TyCtxt<'tcx>,
    scope: &'facts Intrinsics<'facts, 'tcx>,
    nominal: &'facts SourceNominals<'facts, 'tcx>,
    headers: &'facts CheckedHeaders<'tcx>,
    owner: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    root: NativeKey,
    keep: NativeKey,
    erase: NativeKey,
    recommends: DefId,
    kind: SourceHeaderKind,
    declaration: &'facts FnDecl,
    checked: &'facts CheckedSpecDefinitions,
}

impl<'read, 'scope, 'tcx> CheckedSourceRead<'read, 'scope, 'tcx> {
    pub(in crate::reader::declaration_staging) fn function<'facts>(
        &'facts self,
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
    ) -> Result<CheckedSourceFunction<'facts, 'tcx>, String>
    where
        'read: 'facts,
        'scope: 'facts,
    {
        if !std::ptr::eq(*tcx, *self.graph.original.tcx) {
            return Err("the checked forwarding source belongs to another native context".into());
        }
        self.graph.current()?;
        self.nominal.revalidate(tcx)?;
        let id = self
            .read
            .fn_defs
            .iter()
            .find_map(|(id, actual)| (*actual == owner).then_some(*id))
            .ok_or("the checked source function has no actual native binding")?;
        let kind = if id == self.forwarding {
            SourceHeaderKind::InlineForwarder
        } else if id == self.index {
            SourceHeaderKind::Recommendations
        } else {
            return Err("an empty-header dependency uses the ordinary native factory".into());
        };
        let keep = declaration_native::key(tcx, owner.to_def_id());
        let node = self
            .graph
            .original
            .nodes
            .get(&keep)
            .filter(|node| node.owner == owner)
            .ok_or("the checked source function lost its original body owner")?;
        let result = CheckedSourceFunction {
            tcx,
            scope: self.graph.original.scope,
            nominal: self.nominal,
            headers: self
                .graph
                .headers
                .get(&keep)
                .ok_or("missing checked source headers")?,
            owner,
            body: node.body,
            root: declaration_native::key(tcx, self.graph.original.root.to_def_id()),
            keep,
            erase: *self
                .graph
                .original
                .pairs
                .erase(keep)
                .ok_or("missing checked source counterpart")?,
            recommends: self.graph.recommends,
            kind,
            declaration: self
                .read
                .krate
                .fn_decl(id)
                .ok_or("missing checked source declaration")?,
            checked: &self.definitions,
        };
        result.current(tcx, owner)?;
        Ok(result)
    }
}

impl<'tcx> CheckedSourceFunction<'_, 'tcx> {
    fn current(&self, tcx: TyCtxt<'tcx>, owner: LocalDefId) -> Result<(), String> {
        if !std::ptr::eq(*tcx, *self.tcx)
            || owner != self.owner
            || declaration_native::key(tcx, owner.to_def_id()) != self.keep
            || tcx
                .hir_maybe_body_owned_by(owner)
                .is_none_or(|body| !std::ptr::eq(body, self.body))
            || self
                .headers
                .recommends_for(tcx, owner, self.recommends)
                .is_none()
        {
            return Err(
                "the checked source function's native body or original header changed".into(),
            );
        }
        self.nominal.revalidate(tcx)?;
        self.scope.revalidate()?;
        let defining = self
            .checked
            .definitions()
            .any(|function| function.id == self.declaration.id);
        if self.declaration.recommends.is_empty()
            || match self.kind {
                SourceHeaderKind::Recommendations => {
                    !matches!(self.declaration.body, Body::None) || defining
                }
                SourceHeaderKind::InlineForwarder => {
                    !matches!(self.declaration.body, Body::Spec(_)) || !defining
                }
            }
        {
            return Err(
                "the checked source function changed its bodyless or forwarding role".into(),
            );
        }
        Ok(())
    }

    pub(in crate::reader) fn for_factory(
        &self,
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        sources: &crate::declaration_alignment::source_bindings::Sources,
        keep: NativeKey,
        erase: NativeKey,
    ) -> Result<(), String> {
        self.current(tcx, owner)?;
        if !std::ptr::eq(sources, &self.scope.inputs.sources)
            || keep != self.keep
            || erase != self.erase
        {
            return Err(
                "the source semantic function belongs to different factory inputs or counterparts"
                    .into(),
            );
        }
        Ok(())
    }

    pub(in crate::reader) fn owned_requirement(&self) -> OwnedSourceHeader {
        OwnedSourceHeader {
            root: self.root,
            owner: self.keep,
            counterpart: self.erase,
            source: self.scope.inputs.sources.identity(),
            kind: self.kind,
        }
    }
}

impl<'scope, 'tcx> LiveForwardingGraph<'scope, 'tcx> {
    fn current(&self) -> Result<(), String> {
        self.original.current()?;
        if !self.original.nodes.keys().eq(self.headers.keys())
            || !self.original.nodes.keys().eq(self.kinds.keys())
            || self.original.scope.kind(self.recommends) != Some(intrinsics::Kind::Recommends)
        {
            return Err(
                "the finite forwarding input inventory or fresh header builtin changed".into(),
            );
        }
        for (key, node) in &self.original.nodes {
            let headers = self
                .headers
                .get(key)
                .ok_or("missing original forwarding headers")?;
            let recommendation = headers
                .recommends_for(self.original.tcx, node.owner, self.recommends)
                .is_some();
            let empty = headers.empty_for(self.original.tcx, node.owner).is_some();
            if !recommendation && (!empty || self.kinds.get(key) == Some(&Kind::InlineRoot)) {
                return Err("the original finite forwarding header fact changed".into());
            }
        }
        Ok(())
    }

    pub(in crate::reader::declaration_staging) fn observation(&self) -> Result<Value, String> {
        self.current()?;
        let mut value = self.original.observation()?;
        value["finite_inherent_forwarding_inputs"] = json!({
            "bodyless_dependencies": self.kinds.values().filter(|kind| **kind == Kind::Bodyless).count(),
            "original_inline_root": true,
            "bodyless_placeholder_bodies_lowered": false,
            "recommendation_semantics_checked": false,
            "forwarding_equation_authorized": false,
            "import_authorized": false,
        });
        Ok(value)
    }

    /// Use the ordinary mode/type/WF reader over exactly these three original
    /// owners and the separately licensed carrier. The general scalar graph
    /// finalizer and ordinary reader's opaque-datatype refusal stay intact.
    pub(in crate::reader::declaration_staging) fn read_source<'read>(
        &'read self,
        nominal: &'read SourceNominals<'read, 'tcx>,
        work: &mut Work,
    ) -> Result<CheckedSourceRead<'read, 'scope, 'tcx>, String> {
        self.current()?;
        nominal.revalidate(self.original.tcx)?;
        if self.original.nodes.len() != 3
            || self
                .kinds
                .values()
                .filter(|kind| **kind == Kind::InlineRoot)
                .count()
                != 1
        {
            return Err(
                "source forwarding semantics require the complete three-method closure".into(),
            );
        }
        let context = crate::reader::SpecReadContext {
            owners: self
                .original
                .nodes
                .values()
                .map(|node| node.owner)
                .collect(),
            items: self.original.scope.reader_items(),
            source_nominals: Some(nominal),
        };
        let read = crate::reader::read_with_context(
            self.original.tcx,
            crate::reader::ReadOptions::default(),
            None,
            Some(&context),
        );
        work.charge(self.original.tcx, read.spans.len())?;
        if !read.errors.is_empty()
            || read.refusals().next().is_some()
            || !read.verify_refusals.is_empty()
            || !read.pending_item_refusals.is_empty()
            || read.fns.len() != self.original.nodes.len()
            || read.krate.fns.len() != self.original.nodes.len()
            || read
                .fns
                .iter()
                .any(|record| !matches!(record.status, crate::reader::FnStatus::Read(_)))
        {
            return Err(format!(
                "the original forwarding closure did not complete semantic reading: errors={}, refusals={}, verification_refusals={}, pending={}, first_error={:?}, first_refusal={:?}, first_verification_refusal={:?}",
                read.errors.len(),
                read.refusals().count(),
                read.verify_refusals.len(),
                read.pending_item_refusals.len(),
                read.errors.first().map(|error| &error.message),
                read.refusals()
                    .next()
                    .map(|refusal| (&refusal.tag, &refusal.detail)),
                read.verify_refusals
                    .first()
                    .map(|refusal| (refusal.tag, &refusal.detail))
            ));
        }
        if !read.krate.rec_groups.is_empty() {
            return Err(
                "native forwarding recursion needs completed termination verification".into(),
            );
        }
        let strict = trust_vc_vcir::check_crate(&read.krate);
        if !strict.is_empty() {
            return Err(format!(
                "strict original forwarding VcIR checking failed: {strict:?}"
            ));
        }
        let [carrier] = read.krate.adts.as_slice() else {
            return Err(
                "the original forwarding closure lacks its one licensed opaque carrier".into(),
            );
        };
        if carrier.kind != AdtKind::Opaque
            || carrier.type_params.len() != 1
            || !carrier.variants.is_empty()
        {
            return Err(
                "the original forwarding carrier has an unsupported kind, arity or representation"
                    .into(),
            );
        }
        let mut bindings = BTreeMap::new();
        for function in &read.krate.fns {
            let owner = read
                .fn_defs
                .get(&function.id)
                .copied()
                .ok_or("a source forwarding function lost its actual native owner")?;
            let key = declaration_native::key(self.original.tcx, owner.to_def_id());
            if self
                .original
                .nodes
                .get(&key)
                .is_none_or(|node| node.owner != owner)
                || function.mode != Mode::Spec
                || function.role != FnRole::Item
                || function.type_params.len() != 1
                || bindings.insert(key, function.id).is_some()
            {
                return Err(
                    "the complete source forwarding owner, mode, role or binder changed".into(),
                );
            }
        }
        let forwarding = *bindings
            .get(&declaration_native::key(
                self.original.tcx,
                self.original.root.to_def_id(),
            ))
            .ok_or("the source forwarding root lost its current native binding")?;
        let wrapper = read
            .krate
            .fn_decl(forwarding)
            .ok_or("missing source forwarding root")?;
        let Body::Spec(body) = &wrapper.body else {
            return Err("the original forwarding wrapper has no actual Spec body".into());
        };
        let ExprKind::Call { callee: index, .. } = &body.kind else {
            return Err("the original forwarding wrapper is not one direct call".into());
        };
        let index = *index;
        let target = read
            .krate
            .fn_decl(index)
            .ok_or("missing original bodyless forwarding target")?;
        let others = read
            .krate
            .fns
            .iter()
            .filter(|function| function.id != forwarding && function.id != index)
            .collect::<Vec<_>>();
        let [length] = others.as_slice() else {
            return Err(
                "the original forwarding closure lacks its distinct length dependency".into(),
            );
        };
        let length = length.id;
        let length_function = read
            .krate
            .fn_decl(length)
            .ok_or("missing original length declaration")?;
        let carrier_type = Ty::Adt(carrier.id, vec![Ty::Param(0)]);
        let parameters = |function: &FnDecl| {
            function
                .params
                .iter()
                .map(|id| function.local(*id).map(|local| local.ty.clone()))
                .collect::<Option<Vec<_>>>()
        };
        if parameters(wrapper) != Some(vec![carrier_type.clone(), Ty::Int(IntRange::Int)])
            || parameters(target) != Some(vec![carrier_type.clone(), Ty::Int(IntRange::Int)])
            || parameters(length_function) != Some(vec![carrier_type])
            || wrapper.local(wrapper.ret).map(|local| &local.ty) != Some(&Ty::Param(0))
            || target.local(target.ret).map(|local| &local.ty) != Some(&Ty::Param(0))
            || length_function
                .local(length_function.ret)
                .map(|local| &local.ty)
                != Some(&Ty::Int(IntRange::Nat))
            || !matches!(target.body, Body::None)
            || !matches!(length_function.body, Body::None)
            || wrapper.recommends.is_empty()
            || target.recommends.is_empty()
            || !length_function.recommends.is_empty()
        {
            return Err("the original forwarding and uninterpreted signatures or headers differ from the finite fragment".into());
        }
        let definitions = CheckedSpecDefinitions::from_crate_with_forwarders(
            &read.krate,
            &[],
            &[index],
            &[forwarding],
        )
        .map_err(|errors| {
            format!("the original generic forwarding fragment is unavailable: {errors:?}")
        })?;
        if definitions
            .definitions()
            .map(|function| function.id)
            .collect::<Vec<_>>()
            != [forwarding]
        {
            return Err("bodyless source dependencies acquired a checked definition".into());
        }
        self.current()?;
        nominal.revalidate(self.original.tcx)?;
        self.original.scope.revalidate()?;
        Ok(CheckedSourceRead {
            graph: self,
            nominal,
            read,
            definitions,
            forwarding,
            index,
            length,
        })
    }
}

/// Unlike ordinary `capture`, this finite input policy admits native
/// Spec/uninterp/external_body dependencies. It traverses their sealed actual
/// header arguments and never treats their macro placeholder as a definition.
pub(in crate::reader::declaration_staging) fn capture<'scope, 'tcx>(
    tcx: TyCtxt<'tcx>,
    root: LocalDefId,
    scope: &'scope Intrinsics<'scope, 'tcx>,
    pairs: &'scope Pairs,
    work: &mut Work,
) -> Result<LiveForwardingGraph<'scope, 'tcx>, String> {
    scope.current(tcx)?;
    let implementation = tcx.local_parent(root);
    if tcx.def_kind(root) != DefKind::AssocFn
        || tcx.def_kind(implementation) != (DefKind::Impl { of_trait: false })
        || tcx.trait_impl_of_assoc(root.to_def_id()).is_some()
    {
        return Err("finite forwarding inputs require an original inherent method".into());
    }
    let recommends = tcx
        .get_diagnostic_item(Symbol::intern("verus::verus_builtin::recommends"))
        .filter(|definition| scope.kind(*definition) == Some(intrinsics::Kind::Recommends))
        .ok_or("finite forwarding inputs lack their actual fresh recommendation builtin")?;
    let mut pending = vec![root];
    let mut nodes = BTreeMap::new();
    let mut headers_by_key = BTreeMap::new();
    let mut kinds = BTreeMap::new();
    while let Some(owner) = pending.pop() {
        work.charge(tcx, 1)?;
        let key = declaration_native::key(tcx, owner.to_def_id());
        if nodes.contains_key(&key) {
            continue;
        }
        if nodes.len() >= 3 {
            return Err("finite forwarding inputs exceed the three-method closure".into());
        }
        let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
        let parsed = attrs::item_attrs(attributes);
        let original_available = declaration_modes::original_body_available(tcx, owner);
        let ancestor_external = crate::reader::is_external(tcx, owner);
        let counterpart = pairs.erase(key).is_some();
        if tcx.def_kind(owner) != DefKind::AssocFn
            || tcx.local_parent(owner) != implementation
            || tcx.trait_impl_of_assoc(owner.to_def_id()).is_some()
            || !tcx.visibility(owner).is_public()
            || !parsed.verus_macro
            || parsed.mode != Some(Mode::Spec)
            || parsed.external
            || ancestor_external
            || !original_available
            || !counterpart
        {
            let display = tcx
                .def_path_str(owner)
                .chars()
                .take(512)
                .collect::<String>();
            return Err(format!(
                "a finite forwarding member lacks its same-impl public original Spec owner: path={display}, kind={:?}, same_impl={}, trait_impl={}, public={}, macro={}, mode={:?}, external={}, ancestor_external={ancestor_external}, original_body={original_available}, counterpart={counterpart}",
                tcx.def_kind(owner),
                tcx.local_parent(owner) == implementation,
                tcx.trait_impl_of_assoc(owner.to_def_id()).is_some(),
                tcx.visibility(owner).is_public(),
                parsed.verus_macro,
                parsed.mode,
                parsed.external,
            ));
        }
        let kind = if owner == root {
            if !parsed.inline || !parsed.open || parsed.uninterp || parsed.external_body {
                return Err("the original forwarding root is not public open inline Spec".into());
            }
            Kind::InlineRoot
        } else {
            if !parsed.uninterp || !parsed.external_body || parsed.inline {
                return Err(
                    "a finite forwarding dependency is not a bodyless Spec declaration".into(),
                );
            }
            Kind::Bodyless
        };
        let body = tcx
            .hir_maybe_body_owned_by(owner)
            .ok_or("a finite forwarding member has no original body")?;
        original_body(tcx, body)?;
        let headers = match kind {
            Kind::InlineRoot => declaration_headers::check_inline_recommendations(tcx, owner),
            Kind::Bodyless => declaration_headers::check(tcx, owner),
        };
        let argument = headers
            .recommends_for(tcx, owner, recommends)
            .map(|fact| fact.argument());
        if argument.is_none()
            && (kind == Kind::InlineRoot || headers.empty_for(tcx, owner).is_none())
        {
            return Err(
                "a finite forwarding member lacks its complete sealed original header fact".into(),
            );
        }
        let env = ty::TypingEnv::non_body_analysis(tcx, owner.to_def_id());
        let signature = tcx
            .try_normalize_erasing_regions(env, tcx.fn_sig(owner).instantiate_identity())
            .map_err(|_| "a finite forwarding signature cannot be normalized")?;
        let clauses = dispatch::clauses(
            tcx,
            owner.to_def_id(),
            ty::GenericArgs::identity_for_item(tcx, owner.to_def_id()),
            env,
        )?;
        let mut walk = Walk {
            tcx,
            owner,
            scope,
            work,
            bodies: Vec::new(),
            calls: Vec::new(),
            direct_callees: HashSet::new(),
            error: None,
        };
        match kind {
            Kind::InlineRoot => walk.visit_body(body),
            Kind::Bodyless => {
                walk.bodies.push(body);
                if let Some(argument) = argument {
                    walk.visit_expr(argument);
                }
            }
        }
        if let Some(error) = walk.error {
            return Err(error);
        }
        for call in &walk.calls {
            if call.is_intrinsic() {
                continue;
            }
            if call.trait_declaration().is_some() {
                return Err(
                    "a finite forwarding dependency requires unsupported trait selection".into(),
                );
            }
            pending.push(
                call.target()
                    .as_local()
                    .ok_or("a finite forwarding dependency is not an original local method")?,
            );
        }
        nodes.insert(
            key,
            OriginalFunction {
                owner,
                body,
                signature,
                attributes,
                clauses,
                bodies: walk.bodies,
                calls: walk.calls,
            },
        );
        headers_by_key.insert(key, headers);
        kinds.insert(key, kind);
    }
    let graph = LiveForwardingGraph {
        original: LiveGraph {
            tcx,
            root,
            scope,
            pairs,
            nodes,
        },
        headers: headers_by_key,
        kinds,
        recommends,
    };
    graph.current()?;
    Ok(graph)
}
