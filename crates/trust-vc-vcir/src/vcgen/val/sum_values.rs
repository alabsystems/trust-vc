//! Finite sum layouts and typed value operations.
//!
//! These helpers consume admitted IR declarations. They grant no native,
//! imported-body or structural-field authority to a producer.

use super::*;

fn enum_type(mut ty: &Ty) -> Option<(AdtId, &[Ty])> {
    let mut left = 64usize;
    loop {
        left = left.checked_sub(1)?;
        match ty {
            Ty::Ref {
                mutable: false,
                inner,
            } => ty = inner,
            Ty::Adt(id, args) => return Some((*id, args)),
            _ => return None,
        }
    }
}

impl Ctx<'_> {
    fn finite_sum_type(&self, ty: &Ty, stack: &mut Vec<AdtId>, left: &mut usize, work: Option<&std::cell::Cell<usize>>, span: SpanId) -> Option<()> {
        *left = left.checked_sub(1)?;
        if let Some(work) = work { super::super::inline_work::items(work, 1, span).ok()?; }
        match ty {
            Ty::Bool | Ty::Unit | Ty::Param(_) => Some(()),
            Ty::Int(range) => supported_range(*range).ok(),
            Ty::Tuple(fields) => {
                for field in fields {
                    self.finite_sum_type(field, stack, left, work, span)?;
                }
                Some(())
            }
            Ty::Ref {
                mutable: false,
                inner,
            } => self.finite_sum_type(inner, stack, left, work, span),
            Ty::Adt(id, args) => {
                let adt = self.adts.get(id)?;
                if args.len() != adt.type_params.len() {
                    return None;
                }
                for arg in args {
                    self.finite_sum_type(arg, stack, left, work, span)?;
                }
                match adt.kind {
                    AdtKind::Opaque if adt.variants.is_empty() => return Some(()),
                    AdtKind::Struct if adt.variants.len() == 1 => {}
                    AdtKind::Enum if !adt.variants.is_empty() => {}
                    _ => return None,
                }
                if stack.contains(id) {
                    return None;
                }
                stack.push(*id);
                for variant in &adt.variants {
                    *left = left.checked_sub(1)?;
                    for field in &variant.fields {
                        let actual = self.field_type(&field.ty, args, work, span).ok()?;
                        self.finite_sum_type(&actual, stack, left, work, span)?;
                    }
                }
                stack.pop();
                Some(())
            }
            // This is a boxed field recipe, like an actual type parameter;
            // it proves no datatype foundedness or concrete layout. Core WF
            // independently checks the raw dependency graph and definitions.
            Ty::Projection(id, args) if work.is_some() && self.recipe_projection(*id) == Some(args.len()) => {
                for argument in args { self.finite_sum_type(argument, stack, left, work, span)?; }
                Some(())
            }
            _ => None,
        }
    }

    pub(crate) fn register_enum(&self, id: AdtId, span: SpanId) -> Result<(), VcRefusal> {
        self.register_enum_with_work(id, span, None)
    }

    pub(crate) fn register_enum_with_work(&self, id: AdtId, span: SpanId, work: Option<&std::cell::Cell<usize>>) -> Result<(), VcRefusal> {
        if let Some(work) = work { self.ensure_projection_rules(work, span)?; }
        let adt = self.adts.get(&id).ok_or_else(|| {
            refusal(
                "enum-layout",
                "an enum without its actual declaration",
                span,
            )
        })?;
        if adt.kind != AdtKind::Enum || adt.variants.is_empty() {
            return Err(refusal(
                "enum-layout",
                "an empty or incomplete enum layout",
                span,
            ));
        }
        if adt.type_params.len() > 64
            || adt.variants.len() > 64
            || adt
                .variants
                .iter()
                .try_fold(adt.variants.len(), |n, v| n.checked_add(v.fields.len()))
                .is_none_or(|n| n > 64)
        {
            return Err(refusal(
                "enum-layout",
                "a sum layout exceeding its shared declaration bound",
                span,
            ));
        }
        let args: Vec<_> = (0..adt.type_params.len())
            .map(|i| Ty::Param(i as u32))
            .collect();
        self.finite_sum_type(&Ty::Adt(id, args), &mut Vec::new(), &mut 64, work, span)
            .ok_or_else(|| {
                refusal(
                    "enum-layout",
                    "a recursive, mutable or unsupported finite sum layout",
                    span,
                )
            })?;
        let family = ProductFamily::Enum(id);
        let mut left = 64usize;
        let mut variants = Vec::new();
        for variant in &adt.variants {
            let mut fields = Vec::new();
            for field in &variant.fields {
                fields.push(
                    TypeRecipe::product_field(
                        &field.ty,
                        family,
                        &|id| self.recipe_adt(id),
            &|id| self.recipe_projection(id),
                        &mut left)
                    .ok_or_else(|| {
                        refusal(
                            "enum-layout",
                            "an enum field outside its declaration type scope",
                            span,
                        )
                    })?,
                );
            }
            variants.push(fields);
        }
        let registered = match work {
            Some(work) if !self.source.projections.is_empty() => self.types.borrow_mut().register_sum_with_work(id, adt.type_params.len(), variants, work, span)?,
            _ => self.types.borrow_mut().register_sum(id, adt.type_params.len(), variants),
        };
        registered.ok_or_else(|| {
                refusal(
                    "enum-layout",
                    "a conflicting or unsupported sum schema",
                    span,
                )
            })
    }

    fn enum_arguments(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        span: SpanId,
    ) -> Result<(AdtId, Vec<Ty>, Vec<TypeArgument>), VcRefusal> {
        let (id, args) = enum_type(ty).ok_or_else(|| {
            refusal(
                "enum-layout",
                "a sum operation without a shared or owned enum type",
                span,
            )
        })?;
        let work = env.projection_work().map(|work| work.as_ref());
        self.register_enum_with_work(id, span, work)?;
        let arguments = args.iter().map(|ty| match work {
            Some(work) => self.type_argument_with_work(ty, env, span, work),
            None => self.type_argument(ty, env, span),
        }).collect::<Result<Vec<_>, _>>()?;
        let actual = match work {
            Some(work) => args.iter().map(|ty| self.normalize_type(ty, work, span)).collect::<Result<Vec<_>, _>>()?,
            None => args.to_vec(),
        };
        Ok((id, actual, arguments))
    }

    pub(crate) fn construct_enum(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        variant: u32,
        fields: Vec<Val>,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        let (id, args, types) = self.enum_arguments(ty, env, span)?;
        let declaration = self.adts[&id];
        let actual = declaration.variants.get(variant as usize).ok_or_else(|| {
            refusal(
                "enum-layout",
                "a constructor outside its actual variant inventory",
                span,
            )
        })?;
        if actual.fields.len() != fields.len() {
            return Err(refusal(
                "enum-layout",
                "a constructor with an incomplete field inventory",
                span,
            ));
        }
        let mut boxed = Vec::new();
        for (field, value) in actual.fields.iter().zip(fields) {
            let ty = self.field_type(&field.ty, &args, env.projection_work().map(|work| work.as_ref()), span)?;
            boxed.push(self.box_native_value(&ty, env, value, span)?);
        }
        let constructed = match env.projection_work() {
            Some(work) => self.types.borrow_mut().construct_sum_with_work(id, &types, variant, boxed, work, span)?,
            None => self.types.borrow_mut().construct_sum(id, &types, variant, boxed),
        };
        constructed.map(Val::Leaf)
            .ok_or_else(|| refusal("enum-layout", "an incompatible typed sum constructor", span))
    }

    pub(crate) fn test_enum(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        variant: u32,
        value: Val,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        let (id, _, args) = self.enum_arguments(ty, env, span)?;
        let Val::Leaf(value) = value else {
            return Err(refusal(
                "enum-layout",
                "a sum test outside its boxed value layout",
                span,
            ));
        };
        let tested = match env.projection_work() {
            Some(work) => self.types.borrow_mut().test_sum_with_work(id, &args, variant, value, work, span)?,
            None => self.types.borrow_mut().test_sum(id, &args, variant, value),
        };
        tested.map(Val::Leaf)
            .ok_or_else(|| refusal("enum-layout", "an incompatible typed variant test", span))
    }

    pub(crate) fn project_enum(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        variant: u32,
        field: u32,
        value: Val,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        let (id, args, types) = self.enum_arguments(ty, env, span)?;
        let declared = self.adts[&id].variants.get(variant as usize)
            .and_then(|variant| variant.fields.get(field as usize)).ok_or_else(|| {
                refusal(
                    "enum-layout",
                    "a field outside its actual instantiated variant",
                    span,
                )
            })?;
        let field_type = self.field_type(&declared.ty, &args, env.projection_work().map(|work| work.as_ref()), span)?;
        let Val::Leaf(value) = value else {
            return Err(refusal(
                "enum-layout",
                "a sum projection outside its boxed value layout",
                span,
            ));
        };
        let projected = match env.projection_work() {
            Some(work) => self.types.borrow_mut().project_sum_with_work(id, &types, variant, field, value, work, span)?,
            None => self.types.borrow_mut().project_sum(id, &types, variant, field, value),
        }.ok_or_else(|| refusal("enum-layout", "an incompatible typed sum projection", span))?;
        self.unbox_native_value(&field_type, env, projected, span)
    }
}
