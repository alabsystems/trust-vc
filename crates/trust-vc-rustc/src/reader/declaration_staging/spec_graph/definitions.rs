//! Semantic definitions consumed while their original Keep bodies are live.
//!
//! The owned packet contains no compiler lifetime and has no decoder. Its
//! source, correspondence and fresh builtin owner are rejoined before a
//! current client can use its equations.

use super::*;
use crate::declaration_alignment::source_bindings::Sources;
use rustc_span::{RelativeBytePos, Span};
use std::cell::RefCell;
use trust_vc_vcir::{
    Body, CheckedSpecDefinitions, Expr, ExprKind, FnDecl, FnId, FnRole, LocalId, SpanId, Ty,
    VcCrate,
};

#[path = "forwarding.rs"]
mod forwarding;
pub(in crate::reader::declaration_staging) use forwarding::{
    capture as capture_forwarding, LiveForwardingGraph, OwnedSourceFamily,
};
pub(in crate::reader) use forwarding::{CheckedSourceFunction, OwnedSourceHeader};

pub(in crate::reader::declaration_staging) struct OwnedDefinitions {
    source: SourceIdentity,
    functions: Vec<FnDecl>,
    keys: BTreeMap<FnId, (NativeKey, NativeKey)>,
    spans: Vec<AuthoredSpan>,
    architecture: trust_vc_vcir::bitvector::Architecture,
    pointer_width: u32,
}

/// Client-local spans and a complete semantic view, kept separate from the
/// published bodyless declarations. Only this module constructs the packet.
#[derive(Clone)]
pub(in crate::reader) struct ClientDefinitions {
    semantic: VcCrate,
    owners: Vec<FnId>,
    recommendations: Vec<FnId>,
    forwarders: Vec<FnId>,
    generic_owners: BTreeMap<FnId, trust_vc_vcir::AdtId>,
    spans: Vec<Span>,
}

impl<'scope, 'tcx> LiveGraph<'scope, 'tcx> {
    pub(in crate::reader::declaration_staging) fn finalize(
        &self,
        work: &mut Work,
    ) -> Result<OwnedDefinitions, String> {
        self.current()?;
        let mut owners = HashSet::new();
        for node in self.nodes.values() {
            let attributes = attrs::item_attrs(node.attributes);
            let parent = self.tcx.local_parent(node.owner);
            if !self.tcx.visibility(node.owner).is_public()
                || !attributes.open
                || !matches!(self.tcx.def_kind(parent), DefKind::Mod)
            {
                return Err("imported definitions currently require public open free Spec functions; private and trait joins remain unavailable".into());
            }
            owners.insert(node.owner);
        }
        let context = crate::reader::SpecReadContext {
            owners,
            items: self.scope.reader_items(),
            source_nominals: None,
        };
        // This is the ordinary semantic reader over precisely the live
        // dependency closure, including modes, WF, visibility and cycles.
        let read = crate::reader::read_with_context(
            self.tcx,
            crate::reader::ReadOptions::default(),
            None,
            Some(&context),
        );
        work.charge(self.tcx, read.spans.len())?;
        if !read.errors.is_empty()
            || read.refusals().next().is_some()
            || !read.verify_refusals.is_empty()
            || !read.pending_item_refusals.is_empty()
            || read.fns.len() != self.nodes.len()
            || read.krate.fns.len() != self.nodes.len()
            || read
                .fns
                .iter()
                .any(|record| !matches!(record.status, crate::reader::FnStatus::Read(_)))
        {
            return Err(format!(
                "the original Spec closure did not complete semantic reading: errors={}, refusals={}, verification_refusals={}, pending={}, first_error={:?}, first_refusal={:?}, first_verification_refusal={:?}",
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
                "recursive imported definitions require completed native termination verification"
                    .into(),
            );
        }
        let strict = trust_vc_vcir::check_crate(&read.krate);
        if !strict.is_empty() {
            return Err(format!(
                "strict original Spec VcIR checking failed: {strict:?}"
            ));
        }
        let ids = read
            .krate
            .fns
            .iter()
            .map(|function| function.id)
            .collect::<Vec<_>>();
        CheckedSpecDefinitions::from_crate(&read.krate, &ids).map_err(|errors| {
            format!("the original Spec definition fragment is unavailable: {errors:?}")
        })?;
        let mut keys = BTreeMap::new();
        let span_indices = RefCell::new(BTreeMap::new());
        let spans = RefCell::new(Vec::new());
        let owned_span = |id: SpanId| -> Result<SpanId, String> {
            if let Some(mapped) = span_indices.borrow().get(&id).copied() {
                return Ok(mapped);
            }
            let original = read
                .spans
                .get(id.0 as usize)
                .copied()
                .ok_or("a checked Spec definition span is outside its original native table")?;
            let anchor = declaration_native::span(self.tcx, &self.scope.inputs.sources, original)?;
            let mapped = SpanId(
                u32::try_from(spans.borrow().len())
                    .map_err(|_| "too many original definition spans")?,
            );
            spans.borrow_mut().push(anchor);
            span_indices.borrow_mut().insert(id, mapped);
            Ok(mapped)
        };
        let mut functions = Vec::new();
        for function in &read.krate.fns {
            // Check that the entire supported expression environment has a
            // faithful remapping before the live native context is discarded.
            // Only referenced spans belong to this packet; an unused native
            // diagnostic span cannot become a definition's source identity.
            functions.push(map_function(function, &Ok, &owned_span)?);
            let owner = read
                .fn_defs
                .get(&function.id)
                .ok_or("a checked Spec definition lost its native owner")?;
            let keep = declaration_native::key(self.tcx, owner.to_def_id());
            if !self.nodes.contains_key(&keep) {
                return Err(
                    "semantic reading introduced a definition outside the original graph".into(),
                );
            }
            let erase = self
                .pairs
                .erase(keep)
                .copied()
                .ok_or("a checked Spec definition lost its counterpart")?;
            keys.insert(function.id, (keep, erase));
            work.charge(self.tcx, function.locals.len())?;
        }
        self.current()?;
        let packet = OwnedDefinitions {
            source: self.scope.inputs.sources.identity(),
            functions,
            keys,
            spans: spans.into_inner(),
            architecture: read.krate.architecture,
            pointer_width: read.krate.pointer_width,
        };
        Ok(packet)
    }
}

impl OwnedDefinitions {
    pub(in crate::reader::declaration_staging) fn revalidate(
        &self,
        inputs: &Inputs,
        pairs: &Pairs,
    ) -> Result<(), String> {
        if self.source != inputs.sources.identity()
            || self.functions.len() != self.keys.len()
            || self
                .keys
                .values()
                .any(|(keep, erase)| pairs.erase(*keep) != Some(erase))
        {
            return Err("the checked Spec definitions changed source or correspondence".into());
        }
        for span in &self.spans {
            inputs.sources.validate_anchor(span)?;
        }
        Ok(())
    }
}

fn current_span(tcx: TyCtxt<'_>, sources: &Sources, anchor: &AuthoredSpan) -> Result<Span, String> {
    sources.validate_anchor(anchor)?;
    // Resolving every current metadata declaration first registers its actual
    // foreign SourceFiles. Compare native original coordinates back to the
    // approved anchor; normalized offsets are never silently substituted.
    for file in tcx.sess.source_map().files().iter() {
        if file.unnormalized_source_len != anchor.original_file_len
            || file.start_pos.0.checked_add(anchor.bytes.1).is_none()
        {
            continue;
        }
        let lo = file.absolute_position(RelativeBytePos(anchor.bytes.0));
        let hi = file.absolute_position(RelativeBytePos(anchor.bytes.1));
        if !file.contains(lo) || !file.contains(hi) {
            continue;
        }
        let span = Span::with_root_ctxt(lo, hi);
        if declaration_native::span(tcx, sources, span).as_ref() == Ok(anchor) {
            return Ok(span);
        }
    }
    Err("an original definition span has no exact current metadata SourceMap join".into())
}

/// Assemble only graphs whose complete dependency signatures were admitted by
/// the actual client. A refused value definition leaves its already admitted
/// declaration uninterpreted and retains an explicit refusal observation.
pub(in crate::reader::declaration_staging) fn for_client(
    tcx: TyCtxt<'_>,
    library: &StagedLibrary,
    signatures: &BTreeMap<NativeKey, FnDecl>,
    nominals: Vec<trust_vc_vcir::AdtDecl>,
    nominal_ids: &BTreeMap<NativeKey, (trust_vc_vcir::AdtId, usize)>,
) -> Result<(ClientDefinitions, Vec<(NativeKey, String)>), String> {
    // Required source semantics are an invariant of this actual client join,
    // in addition to the owned handoff's constructor check. Missing packets
    // must never reach the optional scalar-definition fallback below.
    for packet in &library.prepared.functions {
        if let Some(requirement) = packet.native.source_header() {
            if !library
                .prepared
                .source_families
                .values()
                .any(|family| family.covers(requirement))
            {
                return Err(
                    "a current native source signature lacks its mandatory semantic family".into(),
                );
            }
        }
    }
    for family in library.prepared.source_families.values() {
        family.validate_functions(&library.prepared.functions)?;
    }
    let mut semantic = VcCrate::new("native imported Spec definitions");
    semantic.pointer_width = u32::try_from(tcx.data_layout.pointer_size().bits())
        .map_err(|_| "invalid client pointer width")?;
    semantic.adts = nominals;
    semantic.fns = signatures.values().cloned().collect();
    let mut spans = Vec::new();
    let mut definitions = BTreeMap::new();
    let mut refused = Vec::new();
    let mut architecture = None;
    for (root, graph) in &library.prepared.spec_definitions {
        graph.revalidate(&library.inputs, &library.prepared.spec_pairs)?;
        if !signatures.contains_key(
            library
                .prepared
                .spec_pairs
                .erase(*root)
                .ok_or("a definition root lost correspondence")?,
        ) {
            continue;
        }
        let available = graph
            .keys
            .values()
            .all(|(_, erase)| signatures.contains_key(erase));
        if !available {
            refused.push((
                *root,
                "a checked Spec dependency lacks its complete current native signature join".into(),
            ));
            continue;
        }
        if graph.pointer_width != semantic.pointer_width
            || architecture.is_some_and(|value| value != graph.architecture)
        {
            return Err(
                "checked imported definitions have incompatible architecture contexts".into(),
            );
        }
        architecture = Some(graph.architecture);
        let ids = graph
            .keys
            .iter()
            .map(|(id, (_, erase))| (*id, signatures[erase].id))
            .collect::<BTreeMap<_, _>>();
        let joined = graph
            .spans
            .iter()
            .map(|anchor| current_span(tcx, &library.inputs.sources, anchor))
            .collect::<Result<Vec<_>, _>>();
        let joined = match joined {
            Ok(joined) => joined,
            Err(reason) => {
                refused.push((*root, reason));
                continue;
            }
        };
        let base = u32::try_from(spans.len()).map_err(|_| "too many imported definition spans")?;
        for function in &graph.functions {
            let id = ids[&function.id];
            if definitions.contains_key(&id) {
                continue;
            }
            let map_span = |span: SpanId| -> Result<SpanId, String> {
                if span.0 as usize >= joined.len() {
                    return Err("a Spec span is outside its owned table".into());
                }
                Ok(SpanId(
                    base.checked_add(span.0)
                        .ok_or("imported span index overflow")?,
                ))
            };
            let mapped = map_function(
                function,
                &|id| {
                    ids.get(&id)
                        .copied()
                        .ok_or_else(|| "a Spec call is outside its native dependency graph".into())
                },
                &map_span,
            )?;
            definitions.insert(id, mapped);
        }
        spans.extend(joined);
    }
    if let Some(architecture) = architecture {
        semantic.architecture = architecture;
    }
    let owners = definitions.keys().copied().collect::<Vec<_>>();
    for function in &mut semantic.fns {
        if let Some(definition) = definitions.remove(&function.id) {
            *function = definition;
        }
    }
    if !definitions.is_empty() {
        return Err("a checked definition has no installed native signature".into());
    }
    // Signature spans are installed from the actual client declarations later;
    // zero is not interpreted as a source position in this semantic-only view.
    CheckedSpecDefinitions::from_crate(&semantic, &owners)
        .map_err(|errors| format!("strict current imported Spec checking failed: {errors:?}"))?;
    let mut client = ClientDefinitions {
        semantic,
        owners,
        recommendations: Vec::new(),
        forwarders: Vec::new(),
        generic_owners: BTreeMap::new(),
        spans,
    };
    for family in library.prepared.source_families.values() {
        family.join(tcx, library, signatures, nominal_ids, &mut client)?;
    }
    client.checked()?;
    Ok((client, refused))
}

impl ClientDefinitions {
    /// Private membership in the complete, already joined source packet.
    /// A signature or an observation alone cannot populate these lists.
    pub(in crate::reader) fn bodyless_recommendation_owner(&self, id: FnId) -> bool {
        self.recommendations.contains(&id)
            && !self.owners.contains(&id)
            && !self.forwarders.contains(&id)
            && self.semantic.fn_decl(id).is_some_and(|function| {
                matches!(function.body, Body::None) && !function.recommends.is_empty()
            })
    }

    fn checked(&self) -> Result<CheckedSpecDefinitions, String> {
        CheckedSpecDefinitions::from_crate_with_forwarders(
            &self.semantic,
            &self.owners,
            &self.recommendations,
            &self.forwarders,
        )
        .map_err(|errors| format!("strict source/imported semantics checking failed: {errors:?}"))
    }

    pub(in crate::reader) fn install(
        &self,
        cx: &crate::reader::Cx<'_>,
    ) -> Result<CheckedSpecDefinitions, String> {
        let spans = self
            .spans
            .iter()
            .map(|span| cx.span_id(*span))
            .collect::<Vec<_>>();
        let mut semantic = self.semantic.clone();
        for function in &mut semantic.fns {
            if let Some(carrier) = self.generic_owners.get(&function.id) {
                *function = forwarding::map_source_function(
                    function,
                    &Ok,
                    &|span| {
                        spans.get(span.0 as usize).copied().ok_or_else(|| {
                            "a current source family span lost its exact table entry".into()
                        })
                    },
                    *carrier,
                    *carrier,
                )?;
            } else if self.owners.contains(&function.id) {
                *function = map_function(function, &Ok, &|span| {
                    spans
                        .get(span.0 as usize)
                        .copied()
                        .ok_or_else(|| "a current Spec span lost its table entry".into())
                })?;
            }
        }
        CheckedSpecDefinitions::from_crate_with_forwarders(
            &semantic,
            &self.owners,
            &self.recommendations,
            &self.forwarders,
        )
        .map_err(|errors| format!("strict installed Spec definition checking failed: {errors:?}"))
    }
}

/// Preserve one complete definition-local environment. Its locals are not the
/// canonical arg/result-only environment of the published imported signature.
fn map_function(
    source: &FnDecl,
    function: &impl Fn(FnId) -> Result<FnId, String>,
    span: &impl Fn(SpanId) -> Result<SpanId, String>,
) -> Result<FnDecl, String> {
    let mut result = source.clone();
    result.id = function(source.id)?;
    result.span = span(source.span)?;
    for local in &mut result.locals {
        scalar(&local.ty)?;
        local.span = span(local.span)?;
    }
    let locals = (0..source.locals.len())
        .map(|index| LocalId(index as u32))
        .collect::<Vec<_>>();
    let local = |id: LocalId| {
        locals
            .get(id.0 as usize)
            .copied()
            .ok_or_else(|| "a definition local is outside its native environment".to_string())
    };
    result.params = source
        .params
        .iter()
        .map(|id| local(*id))
        .collect::<Result<_, _>>()?;
    result.ret = local(source.ret)?;
    for clause in result
        .requires
        .iter_mut()
        .chain(&mut result.ensures)
        .chain(&mut result.recommends)
    {
        clause.expr = map_expr(&clause.expr, function, span, &local)?;
        clause.span = span(clause.span)?;
    }
    for measure in &mut result.decreases {
        *measure = map_expr(measure, function, span, &local)?;
    }
    if let Some(condition) = &mut result.decreases_when {
        *condition = map_expr(condition, function, span, &local)?;
    }
    if let Some(proof) = result.decreases_by {
        result.decreases_by = Some(function(proof)?);
    }
    result.body = match &source.body {
        Body::Spec(expr) => Body::Spec(map_expr(expr, function, span, &local)?),
        _ => return Err("an imported definition requires its actual pure Spec body".into()),
    };
    if result.role != FnRole::Item || !result.type_params.is_empty() {
        return Err(
            "generic and trait definition remapping require their native binder joins".into(),
        );
    }
    Ok(result)
}

fn scalar(ty: &Ty) -> Result<(), String> {
    match ty {
        Ty::Bool | Ty::Unit | Ty::Int(_) => Ok(()),
        _ => Err("imported definition values currently require checked scalar types".into()),
    }
}

fn map_expr(
    source: &Expr,
    function: &impl Fn(FnId) -> Result<FnId, String>,
    span: &impl Fn(SpanId) -> Result<SpanId, String>,
    local: &impl Fn(LocalId) -> Result<LocalId, String>,
) -> Result<Expr, String> {
    scalar(&source.ty)?;
    let recurse = |expr: &Expr| map_expr(expr, function, span, local);
    let kind = match &source.kind {
        ExprKind::Lit(value) => ExprKind::Lit(value.clone()),
        ExprKind::IntegerConstant(value) => ExprKind::IntegerConstant(*value),
        ExprKind::Read(place) if place.projections.is_empty() => {
            let mut place = place.clone();
            place.local = local(place.local)?;
            ExprKind::Read(place)
        }
        ExprKind::Unary {
            op,
            arg,
            check: None,
        } => ExprKind::Unary {
            op: *op,
            arg: Box::new(recurse(arg)?),
            check: None,
        },
        ExprKind::Binary {
            op,
            lhs,
            rhs,
            check: None,
        } => ExprKind::Binary {
            op: *op,
            lhs: Box::new(recurse(lhs)?),
            rhs: Box::new(recurse(rhs)?),
            check: None,
        },
        ExprKind::If {
            cond,
            then_expr,
            else_expr,
        } => ExprKind::If {
            cond: Box::new(recurse(cond)?),
            then_expr: Box::new(recurse(then_expr)?),
            else_expr: Box::new(recurse(else_expr)?),
        },
        ExprKind::Let {
            local: id,
            value,
            body,
        } => ExprKind::Let {
            local: local(*id)?,
            value: Box::new(recurse(value)?),
            body: Box::new(recurse(body)?),
        },
        ExprKind::Call {
            callee,
            type_args,
            args,
        } if type_args.is_empty() => ExprKind::Call {
            callee: function(*callee)?,
            type_args: Vec::new(),
            args: args.iter().map(recurse).collect::<Result<_, _>>()?,
        },
        ExprKind::Cast { arg, kind } => ExprKind::Cast {
            arg: Box::new(recurse(arg)?),
            kind: *kind,
        },
        _ => {
            return Err(
                "an imported Spec expression requires an implemented complete native remapping"
                    .into(),
            );
        }
    };
    Ok(Expr {
        ty: source.ty.clone(),
        span: span(source.span)?,
        kind,
    })
}
