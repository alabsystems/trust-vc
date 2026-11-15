//! Capture transient types from genuine original local declarations.

use std::collections::HashMap;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt};
use rustc_span::Symbol;

use super::super::declaration_policy::{self, OwnedPolicy};
use super::graph::{Declaration, Graph, Type};
use super::{key, original, BuiltinRequirement, BuiltinRole};

const MAX_DATATYPES: usize = 256;
const MAX_VARIANTS: usize = 1_024;
const MAX_FIELDS: usize = 4_096;
const MAX_TYPE_WORK: usize = 16_384;

pub(super) struct Captured {
    pub(super) graph: Graph,
    pub(super) owners: Vec<DefId>,
    pub(super) builtins: Vec<BuiltinRequirement>,
    pub(super) imported: Vec<DefId>,
}

struct Capture<'context, 'tcx> {
    tcx: TyCtxt<'tcx>,
    client: Option<&'context super::super::Cx<'tcx>>,
    graph: Graph,
    owners: Vec<DefId>,
    policies: Vec<OwnedPolicy>,
    indices: HashMap<DefId, usize>,
    builtins: Vec<BuiltinRequirement>,
    type_work: usize,
    fields: usize,
    variants: usize,
    imported: Vec<DefId>,
}

impl<'tcx> Capture<'_, 'tcx> {
    fn imported_policy(
        &mut self,
        definition: DefId,
        arity: usize,
    ) -> Result<Vec<declaration_policy::Recursion>, String> {
        let cx = self
            .client
            .ok_or("a foreign datatype has no current client capability")?;
        let view = cx
            .imported_nominal_policy(definition)
            .ok_or("the foreign datatype has no sealed current client policy")?;
        let policy = view.policy();
        let nominal = policy
            .nominal()
            .ok_or("the imported policy is not nominal")?;
        if definition.is_local()
            || view.definition() != definition
            || cx.adt_id(definition) != Some(view.id())
            || view.arity() != arity
            || arity > 256
            || policy.parameters().len() != arity
            || nominal.recursion().len() != arity
            || !nominal.known_sized()
            || policy
                .parameters()
                .iter()
                .enumerate()
                .any(|(index, parameter)| {
                    parameter.scope != policy.owner() || parameter.index as usize != index
                })
            || nominal
                .recursion()
                .iter()
                .enumerate()
                .any(|(index, parameter)| parameter.parameter as usize != index)
        {
            return Err(
                "the imported native identity, binder and complete recursion policy disagree"
                    .into(),
            );
        }
        // These parameter scope keys intentionally belong to the original
        // Keep check. The registry's sealed correspondence binds them to the
        // actual client Erase definition; no fabricated same-session key is used.
        let parameters = nominal
            .recursion()
            .iter()
            .map(|parameter| parameter.policy)
            .collect();
        if !self.imported.contains(&definition) {
            if self.imported.len() + self.owners.len() >= MAX_DATATYPES {
                return Err("the imported policy inventory exceeds its bound".into());
            }
            self.imported.push(definition);
        }
        Ok(parameters)
    }

    fn node(&mut self, owner: DefId) -> Result<usize, String> {
        if let Some(index) = self.indices.get(&owner) {
            return Ok(*index);
        }
        if !owner.is_local() || !original(self.tcx, owner) {
            return Err(
                "foreign/private or projected datatype representations are not inspected".into(),
            );
        }
        if self.owners.len() + self.imported.len() >= MAX_DATATYPES {
            return Err("reachable native datatype inventory exceeds its bound".into());
        }
        let checked = declaration_policy::check(self.tcx, owner);
        let policy = checked
            .owned_for(self.tcx, owner)
            .ok_or("a reachable local datatype has no supported native generic policy")?;
        let nominal = policy
            .nominal()
            .ok_or("a reachable native declaration is not nominal")?;
        if policy
            .parameters()
            .iter()
            .enumerate()
            .any(|(index, parameter)| {
                parameter.scope != policy.owner() || parameter.index as usize != index
            })
            || nominal
                .recursion()
                .iter()
                .enumerate()
                .any(|(index, parameter)| parameter.parameter as usize != index)
            || nominal.recursion().len() != policy.parameters().len()
        {
            return Err("native nominal binder and recursion-policy indices disagree".into());
        }
        let parameters = nominal
            .recursion()
            .iter()
            .map(|parameter| parameter.policy)
            .collect();
        let index = self.owners.len();
        self.indices.insert(owner, index);
        self.owners.push(owner);
        self.policies.push(policy);
        self.graph.declarations.push(Declaration {
            parameters,
            variants: vec![],
        });
        Ok(index)
    }

    fn require_builtin(&mut self, owner: DefId, role: BuiltinRole) -> Result<(), String> {
        if owner.is_local() || self.tcx.def_kind(owner) != DefKind::Struct {
            return Err(
                "builtin datatype meaning needs an actual foreign selected definition".into(),
            );
        }
        let requirement = BuiltinRequirement {
            role,
            definition: key(self.tcx, owner),
            crate_svh: self.tcx.crate_hash(owner.krate).as_u128(),
        };
        if self.builtins.iter().any(|previous| {
            previous.definition == requirement.definition && previous.role != requirement.role
        }) {
            return Err("one native definition has conflicting builtin roles".into());
        }
        if !self.builtins.contains(&requirement) {
            self.builtins.push(requirement);
        }
        Ok(())
    }

    fn builtin(&self, owner: DefId) -> Option<BuiltinRole> {
        for (name, role) in [
            ("verus::verus_builtin::FnSpec", BuiltinRole::SpecFunction),
            (
                "verus::verus_builtin::int",
                BuiltinRole::MathematicalInteger,
            ),
            ("verus::verus_builtin::nat", BuiltinRole::NaturalNumber),
        ] {
            if self.tcx.get_diagnostic_item(Symbol::intern(name)) == Some(owner) {
                return Some(role);
            }
        }
        (self.tcx.lang_items().owned_box() == Some(owner)).then_some(BuiltinRole::OwnedBox)
    }

    fn arguments(&self, owner: DefId, args: GenericArgsRef<'tcx>) -> Result<Vec<Ty<'tcx>>, String> {
        if args.len() > 256 || args.len() > self.type_work {
            return Err("native datatype argument inventory exceeds its bound".into());
        }
        let generics = self.tcx.generics_of(owner);
        if generics.parent.is_some()
            || generics.own_params.len() != args.len()
            || generics.own_params.iter().any(|parameter| {
                !matches!(
                    parameter.kind,
                    ty::GenericParamDefKind::Type {
                        synthetic: false,
                        ..
                    }
                )
            })
        {
            return Err("a field datatype has unsupported native binders or arity".into());
        }
        args.iter()
            .map(|arg| match arg.kind() {
                ty::GenericArgKind::Type(value) => Ok(value),
                _ => Err("a field datatype has lifetime or const arguments".into()),
            })
            .collect()
    }

    fn ty(&mut self, value: Ty<'tcx>, owner: usize, depth: usize) -> Result<Type, String> {
        self.type_work = self
            .type_work
            .checked_sub(1)
            .ok_or("native field type work exceeds its bound")?;
        if depth > 64 {
            return Err("native field type depth exceeds its bound".into());
        }
        Ok(match value.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => Type::Base,
            ty::Param(parameter) if (parameter.index as usize) < self.graph.declarations[owner].parameters.len() => {
                Type::Parameter(parameter.index)
            }
            ty::Tuple(values) => {
                if values.len() > self.type_work { return Err("native tuple type exceeds its work bound".into()); }
                Type::Product(values.iter().map(|value| self.ty(value, owner, depth + 1)).collect::<Result<_, _>>()?)
            }
            ty::Ref(_, inner, mutability) if !mutability.is_mut() => {
                Type::Decorated(Box::new(self.ty(*inner, owner, depth + 1)?))
            }
            ty::Adt(adt, args) => {
                let definition = adt.did();
                let arguments = self.arguments(definition, args)?;
                match self.builtin(definition) {
                    Some(role @ (BuiltinRole::MathematicalInteger | BuiltinRole::NaturalNumber)) => {
                        if !arguments.is_empty() { return Err("a numeric builtin has unexpected arguments".into()); }
                        self.require_builtin(definition, role)?;
                        Type::Base
                    }
                    Some(BuiltinRole::SpecFunction) => {
                        let [inputs, output] = arguments.as_slice() else {
                            return Err("a native spec function has unexpected arity".into());
                        };
                        let ty::Tuple(inputs) = inputs.kind() else {
                            return Err("native spec-function inputs are not a tuple".into());
                        };
                        self.require_builtin(definition, BuiltinRole::SpecFunction)?;
                        if inputs.len() > self.type_work { return Err("native spec-function inputs exceed their bound".into()); }
                        Type::SpecFunction {
                            inputs: inputs.iter().map(|input| self.ty(input, owner, depth + 1)).collect::<Result<_, _>>()?,
                            output: Box::new(self.ty(*output, owner, depth + 1)?),
                        }
                    }
                    Some(BuiltinRole::OwnedBox) => {
                        let [inner, allocator] = arguments.as_slice() else {
                            return Err("native Box has unexpected arity".into());
                        };
                        let parameter = &self.tcx.generics_of(definition).own_params[1];
                        if !matches!(parameter.kind, ty::GenericParamDefKind::Type { has_default: true, .. }) {
                            return Err("native Box allocator has no declared default".into());
                        }
                        let default = self.tcx.type_of(parameter.def_id).instantiate(self.tcx, args).skip_normalization();
                        if default != *allocator { return Err("custom Box allocator validation is not represented".into()); }
                        self.require_builtin(definition, BuiltinRole::OwnedBox)?;
                        // Pinned Verus decorates the inner type and excludes
                        // its allocator from positivity and base-case checks.
                        Type::Decorated(Box::new(self.ty(*inner, owner, depth + 1)?))
                    }
                    None => {
                        if definition.is_local() {
                            let node = self.node(definition)?;
                            Type::Nominal { node, arguments: arguments.iter()
                                .map(|argument| self.ty(*argument, owner, depth + 1)).collect::<Result<_, _>>()? }
                        } else {
                            let parameters = self.imported_policy(definition, arguments.len())?;
                            Type::Imported { parameters, arguments: arguments.iter()
                                .map(|argument| self.ty(*argument, owner, depth + 1)).collect::<Result<_, _>>()? }
                        }
                    }
                }
            }
            _ => return Err("a native datatype field type needs unsupported bounds, projection or type validation".into()),
        })
    }

    fn fill(&mut self, index: usize) -> Result<(), String> {
        let owner = self.owners[index];
        let adt = self.tcx.adt_def(owner);
        if !adt.is_struct() && !adt.is_enum() {
            return Err("native nominal WF supports structs and enums".into());
        }
        // Verus check_item_struct explicitly gives an external-body struct one
        // empty logical variant. This is an authored language rule, not an
        // inference from missing metadata fields. Enum fields are still checked.
        if adt.is_struct()
            && self.policies[index]
                .nominal()
                .is_some_and(|nominal| nominal.external_body())
        {
            self.graph.declarations[index].variants = vec![vec![]];
            return Ok(());
        }
        self.variants = self
            .variants
            .checked_add(adt.variants().len())
            .filter(|count| *count <= MAX_VARIANTS)
            .ok_or("native variant inventory exceeds its bound")?;
        let mut variants = Vec::new();
        for variant in adt.variants().iter() {
            self.fields = self
                .fields
                .checked_add(variant.fields.len())
                .filter(|count| *count <= MAX_FIELDS)
                .ok_or("native field inventory exceeds its bound")?;
            let mut fields = Vec::new();
            for field in &variant.fields {
                if !field.did.is_local() {
                    return Err("foreign private field types are not validation inputs".into());
                }
                let native = self
                    .tcx
                    .type_of(field.did)
                    .instantiate_identity()
                    .skip_normalization();
                fields.push(self.ty(native, index, 0)?);
            }
            variants.push(fields);
        }
        self.graph.declarations[index].variants = variants;
        Ok(())
    }
}

pub(super) fn capture(tcx: TyCtxt<'_>, owner: DefId) -> Result<Captured, String> {
    capture_in(tcx, owner, None)
}

pub(super) fn capture_client(cx: &super::super::Cx<'_>, owner: DefId) -> Result<Captured, String> {
    capture_in(cx.tcx, owner, Some(cx))
}

fn capture_in<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    client: Option<&super::super::Cx<'tcx>>,
) -> Result<Captured, String> {
    let mut capture = Capture {
        tcx,
        client,
        graph: Graph {
            declarations: vec![],
        },
        owners: vec![],
        policies: vec![],
        indices: HashMap::new(),
        builtins: vec![],
        type_work: MAX_TYPE_WORK,
        variants: 0,
        fields: 0,
        imported: vec![],
    };
    capture.node(owner)?;
    let mut next = 0;
    while next < capture.owners.len() {
        capture.fill(next)?;
        next += 1;
    }
    Ok(Captured {
        graph: capture.graph,
        owners: capture.owners,
        builtins: capture.builtins,
        imported: capture.imported,
    })
}
