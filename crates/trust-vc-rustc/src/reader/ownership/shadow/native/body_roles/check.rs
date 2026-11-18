//! Exact ordinary HIR topology joined to the actual parser allocation map.
//! Success is structural/native data only: original MIR/erasure and the
//! original-to-fresh cohort/role coordinator remain mandatory before admission.

use super::super::super::program as out;
use super::*;
use rustc_ast::{BindingMode, ByRef, LitKind};
use rustc_hir::def::DefKind;
use std::collections::{HashMap, HashSet};

pub(super) fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    expected: &Expected,
    functions: &BTreeMap<FunctionId, LocalDefId>,
    adts: &BTreeMap<AdtId, LocalDefId>,
    allocations: Captured,
) -> Result<BTreeSet<(Site, Role)>, String> {
    let mut check = Check {
        tcx,
        functions,
        adts,
        allocations,
        seen: BTreeSet::new(),
        expressions: HashSet::new(),
        owner: None,
        function: None,
        locals: HashMap::new(),
    };
    for declaration in &expected.program.adts {
        charge(&mut check.allocations.remaining)?;
        let owner = *adts
            .get(&declaration.id)
            .ok_or("missing actual struct owner")?;
        check.owner = Some(owner);
        check.mark((declaration.site, Role::Adt), Family::Adt, None, None)?;
        if declaration.kind != AdtKind::Struct || declaration.variants.len() != 1 {
            return Err("the complete ordinary body path requires struct declarations".into());
        }
        let native = tcx.adt_def(owner);
        if !native.is_struct()
            || native.non_enum_variant().fields.len() != declaration.variants[0].fields.len()
        {
            return Err(
                "the actual struct layout changed before ordinary body correspondence".into(),
            );
        }
        check.mark(
            (declaration.variants[0].site, Role::Variant),
            Family::StructLayout,
            None,
            None,
        )?;
        let frame = Frame {
            generics: &declaration.generics,
            regions: 0,
        };
        for (actual, field) in native
            .non_enum_variant()
            .fields
            .iter()
            .zip(&declaration.variants[0].fields)
        {
            charge(&mut check.allocations.remaining)?;
            let local = actual
                .did
                .as_local()
                .ok_or("a generated struct field is foreign")?;
            let hir::Node::Field(actual_field) = tcx.hir_node_by_def_id(local) else {
                return Err("the selected native field lost its actual HIR declaration".into());
            };
            check.mark(
                (field.site, Role::Field),
                Family::FieldType,
                Some(actual_field.ty.span),
                None,
            )?;
            check.ty(
                tcx.type_of(actual.did)
                    .instantiate_identity()
                    .skip_normalization(),
                &field.ty,
                frame,
            )?;
        }
    }
    for function in &expected.program.functions {
        charge(&mut check.allocations.remaining)?;
        if !function.regions.is_empty() {
            return Err("ordinary body regions still need the full native frame join".into());
        }
        let owner = *functions
            .get(&function.id)
            .ok_or("missing actual function owner")?;
        check.owner = Some(owner);
        check.function = Some(function);
        check.locals.clear();
        check.mark(
            (function.site, Role::Function),
            Family::Function,
            None,
            None,
        )?;
        let body = tcx.hir_body_owned_by(owner);
        if body.params.len() != function.parameters.len()
            || tcx.typeck(owner).tainted_by_errors.is_some()
        {
            return Err("ordinary body parameters or actual native type checking changed".into());
        }
        for (actual, parameter) in body.params.iter().zip(&function.parameters) {
            check.binding(parameter, actual.pat, None)?;
        }
        let hir::ExprKind::Block(wrapper, None) = body.value.kind else {
            return Err("a generated root lost its exact enclosing native block".into());
        };
        if !wrapper.stmts.is_empty() {
            return Err("an unissued statement was inserted before the generated root".into());
        }
        let expression = wrapper
            .expr
            .ok_or("the native wrapper omitted the issued root expression")?;
        check.expr(&function.body, expression, None, 0)?;
    }
    if check.seen.len() != expected.emitted.roles.len()
        || check.seen.iter().ne(expected.emitted.roles.keys())
    {
        return Err(
            "ordinary parser/HIR correspondence did not close the complete issued role set".into(),
        );
    }
    if tcx.dcx().has_errors().is_some() {
        return Err("native diagnostics revoked ordinary body correspondence".into());
    }
    Ok(check.seen)
}

struct Check<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    functions: &'a BTreeMap<FunctionId, LocalDefId>,
    adts: &'a BTreeMap<AdtId, LocalDefId>,
    allocations: Captured,
    seen: BTreeSet<(Site, Role)>,
    expressions: HashSet<hir::HirId>,
    owner: Option<LocalDefId>,
    function: Option<&'a out::Function>,
    locals: HashMap<out::LocalId, (hir::HirId, ty::Ty<'tcx>)>,
}
impl<'tcx> Check<'_, 'tcx> {
    fn mark(
        &mut self,
        role: (Site, Role),
        family: Family,
        span: Option<rustc_span::Span>,
        parent: Option<Site>,
    ) -> Result<(), String> {
        charge(&mut self.allocations.remaining)?;
        let allocation = self
            .allocations
            .nodes
            .get(&role)
            .ok_or("an issued role has no actual parser allocation")?;
        let parent = parent
            .map(|site| {
                self.allocations
                    .nodes
                    .get(&(site, Role::Expression))
                    .map(|node| node.node)
                    .ok_or("a native child lost its actual parent parser allocation")
            })
            .transpose()?;
        if allocation.family != family
            || Some(allocation.owner) != self.owner
            || allocation.parent != parent
            || !allocation.canonical.contains(allocation.inner)
            || span.is_some_and(|span| span != allocation.canonical)
            || !self.seen.insert(role)
        {
            return Err("an ordinary role changed actual parser owner, node kind, parent edge, canonical allocation span or multiplicity".into());
        }
        Ok(())
    }
    fn ty(
        &mut self,
        actual: ty::Ty<'tcx>,
        expected: &Type,
        frame: Frame<'_>,
    ) -> Result<(), String> {
        fn cost(ty: &Type, remaining: &mut usize, depth: usize) -> Result<(), String> {
            charge(remaining)?;
            if depth >= 128 {
                return Err("ordinary type comparison exceeds its depth bound".into());
            }
            match ty {
                Type::Tuple(types) | Type::Adt(_, types) => {
                    for ty in types {
                        cost(ty, remaining, depth + 1)?;
                    }
                }
                Type::Reference { .. } => {
                    return Err("ordinary reference correspondence is not yet closed".into())
                }
                _ => {}
            }
            Ok(())
        }
        cost(expected, &mut self.allocations.remaining, 0)?;
        compare_type(self.tcx, actual, expected, frame, self.adts)
    }
    fn binding(
        &mut self,
        expected: &out::Binding,
        actual: &'tcx hir::Pat<'tcx>,
        parent: Option<Site>,
    ) -> Result<(), String> {
        charge(&mut self.allocations.remaining)?;
        let owner = self.owner.ok_or("binding without native owner")?;
        let hir::PatKind::Binding(BindingMode(ByRef::No, mutability), binding, _, None) =
            actual.kind
        else {
            return Err("the ordinary native binding changed its actual by-value pattern".into());
        };
        if mutability.is_mut() != expected.mutable
            || binding.owner.def_id != owner
            || !matches!(self.tcx.hir_node(actual.hir_id), hir::Node::Pat(current) if std::ptr::eq(current, actual))
        {
            return Err("a native binding changed its allocation, owner or mutability".into());
        }
        self.mark(
            (expected.site, Role::Binding),
            Family::Binding,
            Some(actual.span),
            parent,
        )?;
        let native = self.tcx.typeck(owner).pat_ty(actual);
        let function = self.function.ok_or("binding without current function")?;
        self.ty(
            native,
            &expected.ty,
            Frame {
                generics: &function.generics,
                regions: 0,
            },
        )?;
        if self.locals.insert(expected.id, (binding, native)).is_some() {
            return Err("distinct issued locals reused one native binding role".into());
        }
        let scopes = self.tcx.region_scope_tree(owner);
        if scopes.var_scope(binding.local_id).is_none() {
            return Err("a real native binding lost its lexical storage scope".into());
        }
        Ok(())
    }
    fn adt(
        &mut self,
        native: ty::Ty<'tcx>,
        id: AdtId,
        types: &[Type],
    ) -> Result<ty::AdtDef<'tcx>, String> {
        charge(&mut self.allocations.remaining)?;
        let ty::Adt(adt, arguments) = native.kind() else {
            return Err("a nominal native body role is not an ADT".into());
        };
        if !adt.is_struct()
            || adt.did().as_local() != self.adts.get(&id).copied()
            || arguments.len() != types.len()
        {
            return Err(
                "a native body changed its actual nominal declaration or full argument arity"
                    .into(),
            );
        }
        for (actual, expected) in arguments.iter().zip(types) {
            let actual = actual
                .as_type()
                .ok_or("native field region/const arguments need their complete mapping")?;
            let function = self
                .function
                .ok_or("nominal type without current function")?;
            self.ty(
                actual,
                expected,
                Frame {
                    generics: &function.generics,
                    regions: 0,
                },
            )?;
        }
        Ok(*adt)
    }
    fn expr(
        &mut self,
        expected: &out::Expr,
        actual: &'tcx hir::Expr<'tcx>,
        parent: Option<Site>,
        depth: usize,
    ) -> Result<(), String> {
        charge(&mut self.allocations.remaining)?;
        if depth >= 128 {
            return Err("ordinary native body exceeds its depth bound".into());
        }
        let owner = self.owner.ok_or("expression without native owner")?;
        let typeck = self.tcx.typeck(owner);
        if self.tcx.hir_enclosing_body_owner(actual.hir_id) != owner
            || !matches!(self.tcx.hir_node(actual.hir_id), hir::Node::Expr(current) if std::ptr::eq(current, actual))
            || !typeck.expr_adjustments(actual).is_empty()
            || !self.expressions.insert(actual.hir_id)
        {
            return Err("an ordinary expression changed actual owner/allocation or has an unjoined adjustment".into());
        }
        self.mark(
            (expected.site, Role::Expression),
            Family::Expression,
            Some(actual.span),
            parent,
        )?;
        let child = Some(expected.site);
        match (&expected.kind, actual.kind) {
            (out::ExprKind::Local(id), hir::ExprKind::Path(ref path)) => {
                let (binding, native) = self.locals.get(id).ok_or("issued local has no actual native binding")?;
                if typeck.qpath_res(path, actual.hir_id) != Res::Local(*binding) || typeck.expr_ty(actual) != *native {
                    return Err("a native read changed its actual resolved binding or type".into());
                }
            }
            (out::ExprKind::Unit, hir::ExprKind::Tup(values)) if values.is_empty() && typeck.expr_ty(actual).is_unit() => {}
            (out::ExprKind::Bool(expected), hir::ExprKind::Lit(literal)) if matches!(literal.node, LitKind::Bool(actual) if actual == *expected) && typeck.expr_ty(actual).is_bool() => {}
            (out::ExprKind::Integer { magnitude, ty }, hir::ExprKind::Cast(value, _)) => {
                let hir::ExprKind::Lit(literal) = value.kind else { return Err("an integer cast lost its actual native literal child".into()); };
                if !matches!(literal.node, LitKind::Int(value, _) if value.get() == *magnitude) || typeck.expr_ty(value) != self.tcx.types.u128 {
                    return Err("an issued integer changed its exact magnitude or u128 source type".into());
                }
                let function = self.function.ok_or("integer without function")?;
                self.ty(typeck.expr_ty(actual), ty, Frame { generics: &function.generics, regions: 0 })?;
            }
            (out::ExprKind::Tuple(values), hir::ExprKind::Tup(native)) if values.len() == native.len() => {
                for (expected, actual) in values.iter().zip(native) { self.expr(expected, actual, child, depth + 1)?; }
            }
            (out::ExprKind::TupleField { base, field }, hir::ExprKind::Field(native, _)) => {
                let ty::Tuple(fields) = typeck.expr_ty(native).kind() else { return Err("a tuple projection has a non-tuple native base".into()); };
                if typeck.opt_field_index(actual.hir_id).map(|index| index.as_usize()) != Some(*field)
                    || fields.get(*field).copied() != Some(typeck.expr_ty(actual)) {
                    return Err("a tuple read changed its actual compiler field index/type".into());
                }
                self.expr(base, native, child, depth + 1)?;
            }
            (out::ExprKind::StructField { base, adt, types, field }, hir::ExprKind::Field(native, _)) => {
                let declaration = self.adt(typeck.expr_ty(native), *adt, types)?;
                let index = typeck.opt_field_index(actual.hir_id).ok_or("native struct field lacks its compiler slot")?;
                if index.as_usize() != *field { return Err("a struct read changed its actual compiler field slot".into()); }
                let selected = declaration.non_enum_variant().fields.get(index).ok_or("native field outside its actual declaration")?;
                let ty::Adt(_, arguments) = typeck.expr_ty(native).kind() else { unreachable!() };
                if self.tcx.type_of(selected.did).instantiate(self.tcx, arguments).skip_normalization() != typeck.expr_ty(actual) {
                    return Err("a struct projection changed its actual native field substitution/type".into());
                }
                self.expr(base, native, child, depth + 1)?;
            }
            (out::ExprKind::ConstructStruct { adt, types, fields }, hir::ExprKind::Struct(ref path, native, hir::StructTailExpr::None)) => {
                let declaration = self.adt(typeck.expr_ty(actual), *adt, types)?;
                if typeck.qpath_res(path, actual.hir_id) != Res::Def(DefKind::Struct, declaration.did())
                    || fields.len() != native.len() || native.len() != declaration.non_enum_variant().fields.len() {
                    return Err("a struct constructor changed native resolution or its complete field inventory".into());
                }
                for ((slot, expected), actual) in fields.iter().zip(native) {
                    charge(&mut self.allocations.remaining)?;
                    if typeck.opt_field_index(actual.hir_id).map(|index| index.as_usize()) != Some(*slot) {
                        return Err("a struct constructor changed written evaluation order or compiler field slots".into());
                    }
                    self.expr(expected, actual.expr, child, depth + 1)?;
                }
            }
            (out::ExprKind::AssignPlace { destination, value }, hir::ExprKind::Assign(native, actual_value, _)) => {
                self.expr(destination, native, child, depth + 1)?;
                self.expr(value, actual_value, child, depth + 1)?;
                if typeck.expr_ty(native) != typeck.expr_ty(actual_value) || !typeck.expr_ty(actual).is_unit() {
                    return Err("a native assignment changed exact destination/value/result types".into());
                }
            }
            (out::ExprKind::Assign { destination, value }, hir::ExprKind::Assign(place, native_value, _)) => {
                let hir::ExprKind::Path(ref path) = place.kind else { return Err("an issued direct assignment changed its actual local place".into()); };
                let (binding, native) = self.locals.get(destination).copied().ok_or("an assignment lost its actual local binding")?;
                if typeck.qpath_res(path, place.hir_id) != Res::Local(binding)
                    || typeck.expr_ty(place) != native || !typeck.expr_adjustments(place).is_empty()
                    || !typeck.expr_ty(actual).is_unit()
                { return Err("a direct assignment changed its native binding/type/adjustment relationship".into()); }
                self.expr(value, native_value, child, depth + 1)?;
                if typeck.expr_ty(native_value) != native { return Err("a direct assignment changed its native value type".into()); }
            }
            (out::ExprKind::Call { function, types, arguments }, hir::ExprKind::Call(callee, native_arguments)) => {
                let hir::ExprKind::Path(ref path) = callee.kind else { return Err("an ordinary call changed its native callee grammar".into()); };
                let owner = *self.functions.get(function).ok_or("an ordinary call lacks its allocated native function")?;
                let ty::FnDef(target, actual_types) = typeck.expr_ty(callee).kind() else { return Err("an ordinary call is not an actual native FnDef".into()); };
                if !actual_types.bound_vars().is_empty() { return Err("ordinary call type arguments carry an unjoined native binder".into()); }
                let actual_types = actual_types.no_bound_vars().ok_or("ordinary call type arguments contain an escaping bound variable")?;
                if target.as_local() != Some(owner) || typeck.qpath_res(path, callee.hir_id) != Res::Def(DefKind::Fn, *target)
                    || actual_types != typeck.node_args(callee.hir_id)
                    || actual_types.len() != types.len() || native_arguments.len() != arguments.len()
                { return Err("an ordinary call changed its exact native target or full ordered argument vector".into()); }
                for (actual, expected) in actual_types.iter().zip(types) {
                    let actual = actual.as_type().ok_or("ordinary call region/const arguments lack a complete mapping")?;
                    let current = self.function.ok_or("ordinary call without current native function")?;
                    self.ty(actual, expected, Frame { generics: &current.generics, regions: 0 })?;
                }
                for (expected, actual) in arguments.iter().zip(native_arguments) { self.expr(expected, actual, child, depth + 1)?; }
            }
            (out::ExprKind::Block { statements, tail }, hir::ExprKind::Block(native, None)) if statements.len() == native.stmts.len() => {
                for (expected, actual) in statements.iter().zip(native.stmts) {
                    charge(&mut self.allocations.remaining)?;
                    match (expected, actual.kind) {
                        (out::Statement::Let { binding, initializer }, hir::StmtKind::Let(local)) if local.els.is_none() => {
                            if initializer.is_some() != local.init.is_some() { return Err("a native local changed initialization presence".into()); }
                            // The initializer must resolve old bindings before this declaration is installed.
                            if let (Some(expected), Some(actual)) = (initializer, local.init) { self.expr(expected, actual, child, depth + 1)?; }
                            self.binding(binding, local.pat, child)?;
                        }
                        (out::Statement::Expression(expected), hir::StmtKind::Semi(actual)) => self.expr(expected, actual, child, depth + 1)?,
                        _ => return Err("a native body statement changed its exact issued kind/order".into()),
                    }
                }
                match (tail, native.expr) {
                    (Some(expected), Some(actual)) => self.expr(expected, actual, child, depth + 1)?,
                    (None, None) => {},
                    _ => return Err("a native block changed its normal continuation/tail presence".into()),
                }
            }
            _ => return Err("this ordinary native expression differs from its issued topology or still needs a complete body-role rule".into()),
        }
        Ok(())
    }
}
