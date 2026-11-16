//! The inseparable owned semantics of one checked native forwarding family.
//! No decoder, placeholder body or optional signature-only fallback exists.

use super::*;
use trust_vc_vcir::{AdtDecl, AdtId};

pub(in crate::reader::declaration_staging) struct OwnedSourceFamily {
    source: SourceIdentity,
    root: NativeKey,
    keys: BTreeMap<FnId, (NativeKey, NativeKey)>,
    carrier: AdtDecl,
    carrier_keys: (NativeKey, NativeKey),
    functions: Vec<FnDecl>,
    index: FnId,
    forwarding: FnId,
    spans: Vec<AuthoredSpan>,
    architecture: trust_vc_vcir::bitvector::Architecture,
    pointer_width: u32,
}

impl<'read, 'scope, 'tcx> CheckedSourceRead<'read, 'scope, 'tcx> {
    pub(in crate::reader::declaration_staging) fn required_owners(
        &self,
    ) -> Result<Vec<LocalDefId>, String> {
        [self.index, self.forwarding]
            .iter()
            .map(|id| {
                self.read
                    .fn_defs
                    .get(id)
                    .copied()
                    .ok_or_else(|| "missing source family owner".into())
            })
            .collect()
    }

    pub(in crate::reader::declaration_staging) fn into_owned_family(
        &self,
        work: &mut Work,
    ) -> Result<OwnedSourceFamily, String> {
        self.graph.current()?;
        let carrier_keys = self.nominal.native_pair(self.graph.original.tcx)?;
        let carrier = self
            .read
            .krate
            .adts
            .first()
            .ok_or("missing checked source carrier")?;
        let span_indices = RefCell::new(BTreeMap::new());
        let spans = RefCell::new(Vec::new());
        let owned_span = |id: SpanId| -> Result<SpanId, String> {
            if let Some(mapped) = span_indices.borrow().get(&id).copied() {
                return Ok(mapped);
            }
            let span = self
                .read
                .spans
                .get(id.0 as usize)
                .copied()
                .ok_or("a source family span is outside the actual native table")?;
            let anchor = declaration_native::span(
                self.graph.original.tcx,
                &self.graph.original.scope.inputs.sources,
                span,
            )?;
            let id_owned = SpanId(
                u32::try_from(spans.borrow().len()).map_err(|_| "too many source family spans")?,
            );
            spans.borrow_mut().push(anchor);
            span_indices.borrow_mut().insert(id, id_owned);
            Ok(id_owned)
        };
        let mut keys = BTreeMap::new();
        let mut functions = Vec::new();
        for function in &self.read.krate.fns {
            let owner = self
                .read
                .fn_defs
                .get(&function.id)
                .ok_or("missing native source family function")?;
            let keep = declaration_native::key(self.graph.original.tcx, owner.to_def_id());
            let erase = *self
                .graph
                .original
                .pairs
                .erase(keep)
                .ok_or("missing source family counterpart")?;
            keys.insert(function.id, (keep, erase));
            functions.push(map_function(
                function,
                &Ok,
                &owned_span,
                carrier.id,
                carrier.id,
            )?);
            work.charge(self.graph.original.tcx, function.locals.len())?;
        }
        let mut carrier = carrier.clone();
        carrier.span = owned_span(carrier.span)?;
        let result = OwnedSourceFamily {
            source: self.graph.original.scope.inputs.sources.identity(),
            root: declaration_native::key(
                self.graph.original.tcx,
                self.graph.original.root.to_def_id(),
            ),
            keys,
            carrier,
            carrier_keys,
            functions,
            index: self.index,
            forwarding: self.forwarding,
            spans: spans.into_inner(),
            architecture: self.read.krate.architecture,
            pointer_width: self.read.krate.pointer_width,
        };
        result.revalidate(self.graph.original.scope.inputs, self.graph.original.pairs)?;
        self.graph.current()?;
        self.nominal.revalidate(self.graph.original.tcx)?;
        Ok(result)
    }
}

impl OwnedSourceFamily {
    pub(in crate::reader::declaration_staging) fn root(&self) -> NativeKey {
        self.root
    }

    pub(in crate::reader::declaration_staging) fn covers(
        &self,
        requirement: &OwnedSourceHeader,
    ) -> bool {
        let id = match requirement.kind {
            SourceHeaderKind::Recommendations => self.index,
            SourceHeaderKind::InlineForwarder => self.forwarding,
        };
        requirement.source == self.source
            && requirement.root == self.root
            && self.keys.get(&id) == Some(&(requirement.owner, requirement.counterpart))
    }

    pub(in crate::reader::declaration_staging) fn validate_functions<'a>(
        &self,
        functions: impl IntoIterator<Item = &'a keep::CheckedFunctionInputs>,
    ) -> Result<(), String> {
        let functions = functions.into_iter().collect::<Vec<_>>();
        for (id, (keep, erase)) in &self.keys {
            let mut matching = functions.iter().filter(|packet| {
                packet.native.keep_key() == *keep && packet.native.erase_key() == *erase
            });
            let packet = matching
                .next()
                .ok_or("an atomic source family lacks its exact native function")?;
            if matching.next().is_some()
                || if *id == self.index || *id == self.forwarding {
                    packet
                        .native
                        .source_header()
                        .is_none_or(|requirement| !self.covers(requirement))
                } else {
                    packet.native.source_header().is_some()
                }
            {
                return Err(
                    "an atomic source family has inconsistent native function requirements".into(),
                );
            }
        }
        Ok(())
    }

    pub(in crate::reader::declaration_staging) fn revalidate(
        &self,
        inputs: &Inputs,
        pairs: &Pairs,
    ) -> Result<(), String> {
        if self.source != inputs.sources.identity()
            || self.keys.len() != 3
            || self.functions.len() != 3
            || self.index == self.forwarding
            || self.keys.get(&self.forwarding).map(|pair| pair.0) != Some(self.root)
            || self
                .keys
                .values()
                .any(|(keep, erase)| pairs.erase(*keep) != Some(erase))
            || self.carrier.kind != AdtKind::Opaque
            || self.carrier.type_params.len() != 1
            || !self.carrier.variants.is_empty()
        {
            return Err(
                "the owned source family changed its source, native pairs or opaque identity"
                    .into(),
            );
        }
        for span in &self.spans {
            inputs.sources.validate_anchor(span)?;
        }
        Ok(())
    }

    /// Missing dependencies, carriers or spans are errors for this required
    /// family. They never leave its signatures installed as plain UFs.
    pub(in crate::reader::declaration_staging) fn join(
        &self,
        tcx: TyCtxt<'_>,
        library: &StagedLibrary,
        signatures: &BTreeMap<NativeKey, FnDecl>,
        nominal_ids: &BTreeMap<NativeKey, (AdtId, usize)>,
        client: &mut ClientDefinitions,
    ) -> Result<(), String> {
        self.revalidate(&library.inputs, &library.prepared.spec_pairs)?;
        let (_, counterpart) =
            crate::reader::declaration_staging::capability::facts::correspondence(
                library,
                self.carrier_keys.0,
            )?;
        let (carrier, arity) = nominal_ids
            .get(&self.carrier_keys.1)
            .copied()
            .ok_or("a required source carrier lacks its actual licensed client identity")?;
        if counterpart.key != self.carrier_keys.1
            || arity != 1
            || client
                .semantic
                .adts
                .iter()
                .find(|adt| adt.id == carrier)
                .is_none_or(|adt| {
                    adt.kind != AdtKind::Opaque
                        || adt.type_params.len() != 1
                        || !adt.variants.is_empty()
                })
            || self.pointer_width != client.semantic.pointer_width
            || ((!client.owners.is_empty() || !client.generic_owners.is_empty())
                && self.architecture != client.semantic.architecture)
        {
            return Err(
                "the required source family has incompatible current carrier or architecture"
                    .into(),
            );
        }
        let ids = self.keys.iter().map(|(id, (_, erase))| {
            signatures.get(erase).map(|function| (*id, function.id))
                .ok_or_else(|| "a required source function lacks its complete current native signature join".to_string())
        }).collect::<Result<BTreeMap<_, _>, _>>()?;
        let joined = self
            .spans
            .iter()
            .map(|anchor| current_span(tcx, &library.inputs.sources, anchor))
            .collect::<Result<Vec<_>, _>>()?;
        let base = u32::try_from(client.spans.len()).map_err(|_| "too many client source spans")?;
        let span = |id: SpanId| -> Result<SpanId, String> {
            if id.0 as usize >= joined.len() {
                return Err("source family span outside owned table".into());
            }
            Ok(SpanId(
                base.checked_add(id.0)
                    .ok_or("source family span overflow")?,
            ))
        };
        for source in &self.functions {
            let mapped = map_function(
                source,
                &|id| {
                    ids.get(&id)
                        .copied()
                        .ok_or_else(|| "source family call outside native graph".into())
                },
                &span,
                self.carrier.id,
                carrier,
            )?;
            let actual = &signatures[&self.keys[&source.id].1];
            same_signature(&mapped, actual)?;
            let position = client
                .semantic
                .fns
                .iter()
                .position(|function| function.id == mapped.id)
                .ok_or("required native source signature missing from semantic view")?;
            if client.owners.contains(&mapped.id)
                || client.forwarders.contains(&mapped.id)
                || client.recommendations.contains(&mapped.id)
            {
                return Err("required source family overlaps another semantic owner".into());
            }
            client.semantic.fns[position] = mapped;
            client.generic_owners.insert(ids[&source.id], carrier);
        }
        client.semantic.architecture = self.architecture;
        client.recommendations.push(ids[&self.index]);
        client.forwarders.push(ids[&self.forwarding]);
        client.spans.extend(joined);
        client.checked()?;
        Ok(())
    }
}

fn same_signature(source: &FnDecl, actual: &FnDecl) -> Result<(), String> {
    fn local(
        function: &FnDecl,
        id: LocalId,
    ) -> Option<(
        &Ty,
        Mode,
        bool,
        trust_vc_vcir::DeclProphecy,
        trust_vc_vcir::LocalKind,
    )> {
        function.local(id).map(|local| {
            (
                &local.ty,
                local.mode,
                local.mutable,
                local.prophecy,
                local.kind,
            )
        })
    }
    if source.id != actual.id
        || source.mode != actual.mode
        || source.kind != actual.kind
        || source.type_params.len() != 1
        || actual.type_params.len() != 1
        || source.params.len() != actual.params.len()
        || source
            .params
            .iter()
            .zip(&actual.params)
            .any(|(a, b)| local(source, *a) != local(actual, *b))
        || local(source, source.ret) != local(actual, actual.ret)
        || source.attrs.prophetic != actual.attrs.prophetic
        || actual.role != FnRole::Imported
        || !matches!(actual.body, Body::None)
    {
        return Err(
            "required source semantics differ from the actual current native function signature"
                .into(),
        );
    }
    Ok(())
}

fn map_ty(ty: &Ty, original: AdtId, current: AdtId) -> Result<Ty, String> {
    Ok(match ty {
        Ty::Bool | Ty::Unit | Ty::Int(_) | Ty::Param(0) => ty.clone(),
        Ty::Adt(id, args) if *id == original && args.as_slice() == [Ty::Param(0)] => {
            Ty::Adt(current, args.clone())
        }
        _ => {
            return Err(
                "source family type lacks its exact flattened binder or opaque carrier join".into(),
            );
        }
    })
}

pub(in crate::reader::declaration_staging::spec_graph::definitions) fn map_function(
    source: &FnDecl,
    function: &impl Fn(FnId) -> Result<FnId, String>,
    span: &impl Fn(SpanId) -> Result<SpanId, String>,
    original: AdtId,
    current: AdtId,
) -> Result<FnDecl, String> {
    let mut mapped = source.clone();
    mapped.id = function(source.id)?;
    mapped.span = span(source.span)?;
    if source.role != FnRole::Item || source.type_params.len() != 1 {
        return Err("source family role or binder changed".into());
    }
    for local in &mut mapped.locals {
        local.ty = map_ty(&local.ty, original, current)?;
        local.span = span(local.span)?;
    }
    let local = |id: LocalId| {
        if id.0 as usize >= source.locals.len() {
            Err("source family local outside complete source table".to_string())
        } else {
            Ok(id)
        }
    };
    for id in &source.params {
        local(*id)?;
    }
    local(source.ret)?;
    for clause in &mut mapped.recommends {
        clause.expr = map_expr(&clause.expr, function, span, &local, original, current)?;
        clause.span = span(clause.span)?;
    }
    if !source.requires.is_empty()
        || !source.ensures.is_empty()
        || source.unwind.is_some()
        || !source.decreases.is_empty()
        || source.decreases_when.is_some()
        || source.decreases_by.is_some()
    {
        return Err("source family contains an unsupported semantic header".into());
    }
    mapped.body = match &source.body {
        Body::None => Body::None,
        Body::Spec(expr) => Body::Spec(map_expr(expr, function, span, &local, original, current)?),
        _ => {
            return Err(
                "source family requires an actual Spec body or a bodyless declaration".into(),
            );
        }
    };
    Ok(mapped)
}

fn map_expr(
    source: &Expr,
    function: &impl Fn(FnId) -> Result<FnId, String>,
    span: &impl Fn(SpanId) -> Result<SpanId, String>,
    local: &impl Fn(LocalId) -> Result<LocalId, String>,
    original: AdtId,
    current: AdtId,
) -> Result<Expr, String> {
    let recurse = |expr: &Expr| map_expr(expr, function, span, local, original, current);
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
        ExprKind::Cast { arg, kind } => ExprKind::Cast {
            arg: Box::new(recurse(arg)?),
            kind: *kind,
        },
        ExprKind::Call {
            callee,
            type_args,
            args,
        } => ExprKind::Call {
            callee: function(*callee)?,
            type_args: type_args
                .iter()
                .map(|ty| map_ty(ty, original, current))
                .collect::<Result<_, _>>()?,
            args: args.iter().map(recurse).collect::<Result<_, _>>()?,
        },
        _ => return Err("source family expression lacks a complete finite remapping".into()),
    };
    Ok(Expr {
        ty: map_ty(&source.ty, original, current)?,
        span: span(source.span)?,
        kind,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_vcir::{DeclProphecy, DefHash, FnAttrs, FnKind, LocalDecl, LocalKind, Place};

    fn carrier(value: u64) -> AdtId {
        AdtId(DefHash::new(value, 0))
    }
    fn function() -> FnDecl {
        let local = |ty, kind| LocalDecl {
            name: String::new(),
            ty,
            mode: Mode::Spec,
            prophecy: DeclProphecy::Default,
            mutable: false,
            kind,
            span: SpanId(1),
        };
        FnDecl {
            id: FnId(DefHash::new(7, 0)),
            name: "source".into(),
            span: SpanId(1),
            mode: Mode::Spec,
            role: FnRole::Item,
            kind: FnKind::Function,
            type_params: vec!["A".into()],
            // Deliberately differs from the client's canonical argument/return
            // ordering. Expressions must retain these actual local indices.
            locals: vec![
                local(Ty::Param(0), LocalKind::Return),
                local(Ty::int(), LocalKind::Param),
                local(Ty::Adt(carrier(1), vec![Ty::Param(0)]), LocalKind::Param),
            ],
            params: vec![LocalId(2), LocalId(1)],
            ret: LocalId(0),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            unwind: None,
            decreases: vec![],
            decreases_when: None,
            decreases_by: None,
            attrs: FnAttrs::default(),
            body: Body::None,
        }
    }

    #[test]
    fn source_family_remap_preserves_source_local_indices_and_bodyless_role() {
        let source = function();
        let mapped =
            map_function(&source, &Ok, &|_| Ok(SpanId(9)), carrier(1), carrier(2)).unwrap();
        assert_eq!(mapped.params, [LocalId(2), LocalId(1)]);
        assert_eq!(mapped.ret, LocalId(0));
        assert_eq!(mapped.locals[2].ty, Ty::Adt(carrier(2), vec![Ty::Param(0)]));
        assert!(matches!(mapped.body, Body::None));
        let mut actual = mapped.clone();
        actual.role = FnRole::Imported;
        actual.locals = vec![
            mapped.locals[2].clone(),
            mapped.locals[1].clone(),
            mapped.locals[0].clone(),
        ];
        actual.params = vec![LocalId(0), LocalId(1)];
        actual.ret = LocalId(2);
        same_signature(&mapped, &actual).unwrap();
        actual.params.reverse();
        assert!(same_signature(&mapped, &actual).is_err());
        actual.params.reverse();
        actual.locals[0].mode = Mode::Exec;
        assert!(same_signature(&mapped, &actual).is_err());
    }

    #[test]
    fn source_family_remap_rejects_foreign_carriers_and_incomplete_binders() {
        let mut source = function();
        assert!(map_function(&source, &Ok, &Ok, carrier(9), carrier(2)).is_err());
        source.locals[0].ty = Ty::Param(1);
        assert!(map_function(&source, &Ok, &Ok, carrier(1), carrier(2)).is_err());
        source.locals[0].ty = Ty::Param(0);
        source.type_params.push("B".into());
        assert!(map_function(&source, &Ok, &Ok, carrier(1), carrier(2)).is_err());
    }

    #[test]
    fn source_family_remap_rejects_missing_call_joins_and_preserves_call_arguments() {
        let mut source = function();
        let argument = Expr {
            ty: Ty::Adt(carrier(1), vec![Ty::Param(0)]),
            span: SpanId(1),
            kind: ExprKind::Read(Place::local(LocalId(2))),
        };
        source.body = Body::Spec(Expr {
            ty: Ty::Param(0),
            span: SpanId(1),
            kind: ExprKind::Call {
                callee: FnId(DefHash::new(8, 0)),
                type_args: vec![Ty::Param(0)],
                args: vec![argument],
            },
        });
        let joined = |id| {
            if id == source.id {
                Ok(id)
            } else {
                Err("missing native dependency".into())
            }
        };
        assert!(map_function(&source, &joined, &Ok, carrier(1), carrier(2)).is_err());
        let mapped = map_function(&source, &Ok, &Ok, carrier(1), carrier(2)).unwrap();
        let Body::Spec(Expr {
            kind: ExprKind::Call {
                type_args, args, ..
            },
            ..
        }) = mapped.body
        else {
            panic!("lost original call");
        };
        assert_eq!(type_args, [Ty::Param(0)]);
        assert_eq!(args[0].ty, Ty::Adt(carrier(2), vec![Ty::Param(0)]));
        assert!(
            matches!(&args[0].kind,ExprKind::Read(place) if place.local == LocalId(2) && place.projections.is_empty())
        );
    }
}
