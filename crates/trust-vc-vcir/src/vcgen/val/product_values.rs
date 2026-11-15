//! Conversions between source formal layouts and actual native products.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[derive(Clone, Copy)]
pub(crate) enum FormalPosition {
    SpecParameter(usize),
    NativeParameter(usize),
    Result,
}

pub(crate) struct FormalValue<'a> {
    pub(crate) position: FormalPosition,
    pub(crate) actual_ty: &'a Ty,
    pub(crate) type_args: &'a [Ty],
    pub(crate) caller: &'a TypeEnv,
    pub(crate) callee: &'a TypeEnv,
    pub(crate) span: SpanId,
}

struct Layout {
    family: ProductFamily,
    arguments: Vec<Ty>,
    children: Vec<Ty>,
}

struct Codec<'a, 'ctx> {
    ctx: &'a Ctx<'ctx>,
    caller: &'a TypeEnv,
    callee: &'a TypeEnv,
    span: SpanId,
    left: usize,
}

impl Codec<'_, '_> {
    fn charge(&mut self, n: usize) -> Result<(), VcRefusal> {
        self.left = self.left.checked_sub(n).ok_or_else(|| {
            refusal(
                "generic-product",
                "a product conversion exceeding its shared type/layout bound",
                self.span,
            )
        })?;
        Ok(())
    }

    fn actual_type(&mut self, ty: &Ty) -> Result<TypeArgument, VcRefusal> {
        let recipe = TypeRecipe::registered_with_work(
            ty,
            self.caller.owner(),
            &|id| self.ctx.recipe_adt(id),
            &mut self.left,
        )
        .ok_or_else(|| {
            refusal(
                "generic-product",
                "an unsupported actual product type recipe",
                self.span,
            )
        })?;
        self.ctx
            .types
            .borrow_mut()
            .argument(&recipe, self.caller)
            .ok_or_else(|| {
                refusal(
                    "generic-product",
                    "a product type argument outside its caller scope",
                    self.span,
                )
            })
    }

    fn layout(&mut self, ty: &Ty, register: bool) -> Result<Layout, VcRefusal> {
        self.charge(1)?;
        if let Ty::Ref {
            mutable: false,
            inner,
        } = ty
        {
            return self.layout(inner, register);
        }
        let (family, arguments, children, fields) = match ty {
            Ty::Unit => (ProductFamily::Unit, Vec::new(), Vec::new(), Vec::new()),
            Ty::Tuple(children) => {
                self.charge(children.len())?;
                let family = ProductFamily::Tuple(u32::try_from(children.len()).map_err(|_| {
                    refusal(
                        "generic-product",
                        "a tuple arity outside the product ABI",
                        self.span,
                    )
                })?);
                let fields = if register {
                    (0..children.len())
                        .map(|index| TypeRecipe::ProductParameter {
                            owner: family,
                            index: index as u32,
                        })
                        .collect()
                } else {
                    Vec::new()
                };
                (family, children.clone(), children.clone(), fields)
            }
            Ty::Adt(id, args) => {
                let adt = self.ctx.adts.get(id).ok_or_else(|| {
                    refusal(
                        "generic-product",
                        "an unknown product declaration",
                        self.span,
                    )
                })?;
                if adt.kind != AdtKind::Struct
                    || adt.variants.len() != 1
                    || args.len() != adt.type_params.len()
                {
                    return Err(refusal(
                        "generic-product",
                        "a product requiring a finite transparent struct layout",
                        self.span,
                    ));
                }
                let family = ProductFamily::Struct(*id);
                let declared = &adt.variants[0].fields;
                self.charge(args.len().checked_add(declared.len()).ok_or_else(|| {
                    refusal("generic-product", "product layout size overflow", self.span)
                })?)?;
                let mut fields = Vec::new();
                let mut children = Vec::new();
                for field in declared {
                    if register {
                        fields.push(
                            TypeRecipe::product_field(
                                &field.ty,
                                family,
                                &|id| self.ctx.recipe_adt(id),
                                &mut self.left,
                            )
                            .ok_or_else(|| {
                                refusal(
                                    "generic-product",
                                    "an unsupported product field recipe",
                                    self.span,
                                )
                            })?,
                        );
                    }
                    children.push(field.ty.subst(args));
                }
                (family, args.clone(), children, fields)
            }
            _ => {
                return Err(refusal(
                    "generic-product",
                    "a non-product native value",
                    self.span,
                ))
            }
        };
        if register {
            self.ctx
                .types
                .borrow_mut()
                .register_product(family, arguments.len(), fields)
                .ok_or_else(|| {
                    refusal(
                        "generic-product",
                        "a conflicting or malformed product schema",
                        self.span,
                    )
                })?;
        }
        Ok(Layout {
            family,
            arguments,
            children,
        })
    }

    fn arguments(&mut self, layout: &Layout) -> Result<Vec<TypeArgument>, VcRefusal> {
        layout
            .arguments
            .iter()
            .map(|arg| self.actual_type(arg))
            .collect()
    }

    fn box_whole(&mut self, ty: &Ty, native: &Shape, value: Val) -> Result<Term, VcRefusal> {
        self.charge(1)?;
        match (native, value) {
            (Shape::Leaf(leaf), Val::Leaf(value)) if value.sort() == leaf.sort() => {
                if value.sort() == Sort::Poly {
                    return Ok(value);
                }
                let identity = self.actual_type(ty)?;
                self.ctx
                    .types
                    .borrow_mut()
                    .box_value(
                        leaf.sort(),
                        identity.identity().clone(),
                        leaf.bounds(),
                        value,
                    )
                    .ok_or_else(|| {
                        refusal(
                            "generic-product",
                            "an incompatible native leaf in a product",
                            self.span,
                        )
                    })
            }
            (Shape::Node(shapes), Val::Node(values)) => {
                let layout = self.layout(ty, true)?;
                if values.len() != shapes.len() || values.len() != layout.children.len() {
                    return Err(refusal(
                        "generic-product",
                        "a product with inconsistent native field order or arity",
                        self.span,
                    ));
                }
                let args = self.arguments(&layout)?;
                let mut fields = Vec::new();
                for ((child, shape), value) in layout.children.iter().zip(shapes).zip(values) {
                    fields.push(self.box_whole(child, shape, value)?);
                }
                self.ctx
                    .types
                    .borrow_mut()
                    .pack_product(layout.family, &args, fields)
                    .ok_or_else(|| {
                        refusal(
                            "generic-product",
                            "a product pack with an incompatible signature",
                            self.span,
                        )
                    })
            }
            _ => Err(refusal(
                "generic-product",
                "a value outside its native product layout",
                self.span,
            )),
        }
    }

    fn unbox_whole(&mut self, ty: &Ty, native: &Shape, value: Term) -> Result<Val, VcRefusal> {
        self.charge(1)?;
        if value.sort() != Sort::Poly {
            return Err(refusal(
                "generic-product",
                "a product unbox requires Poly",
                self.span,
            ));
        }
        match native {
            Shape::Leaf(leaf) if leaf.sort() == Sort::Poly => Ok(Val::Leaf(value)),
            Shape::Leaf(leaf) => {
                let identity = self.actual_type(ty)?;
                self.ctx
                    .types
                    .borrow_mut()
                    .unbox_value(
                        leaf.sort(),
                        identity.identity().clone(),
                        leaf.bounds(),
                        value,
                    )
                    .map(Val::Leaf)
                    .ok_or_else(|| {
                        refusal(
                            "generic-product",
                            "an incompatible product leaf projection",
                            self.span,
                        )
                    })
            }
            Shape::Node(shapes) => {
                let layout = self.layout(ty, true)?;
                if shapes.len() != layout.children.len() {
                    return Err(refusal(
                        "generic-product",
                        "a product projection with the wrong field arity",
                        self.span,
                    ));
                }
                let args = self.arguments(&layout)?;
                let fields = self
                    .ctx
                    .types
                    .borrow_mut()
                    .project_product(layout.family, &args, value)
                    .ok_or_else(|| {
                        refusal(
                            "generic-product",
                            "a product projection with an incompatible signature",
                            self.span,
                        )
                    })?;
                let mut values = Vec::new();
                for ((child, shape), field) in layout.children.iter().zip(shapes).zip(fields) {
                    values.push(self.unbox_whole(child, shape, field)?);
                }
                Ok(Val::Node(values))
            }
        }
    }

    fn convert(
        &mut self,
        ty: &Ty,
        native: &Shape,
        formal: &Shape,
        value: Val,
        boxing: bool,
    ) -> Result<Val, VcRefusal> {
        self.charge(1)?;
        if let Shape::Leaf(LeafTy::Poly(index)) = formal {
            let expected = {
                let mut vocabulary = self.ctx.types.borrow_mut();
                let recipe = vocabulary.recipe(*index).cloned().ok_or_else(|| {
                    refusal(
                        "generic-product",
                        "an unknown formal type recipe",
                        self.span,
                    )
                })?;
                vocabulary.argument(&recipe, self.callee).ok_or_else(|| {
                    refusal(
                        "generic-product",
                        "a formal product type outside its callee scope",
                        self.span,
                    )
                })?
            };
            if self.actual_type(ty)? != expected {
                return Err(refusal(
                    "generic-product",
                    "formal and actual decoration/type identities disagree",
                    self.span,
                ));
            }
            if boxing {
                return self.box_whole(ty, native, value).map(Val::Leaf);
            }
            let Val::Leaf(value) = value else {
                return Err(refusal(
                    "generic-product",
                    "a boxed formal product is not one Poly leaf",
                    self.span,
                ));
            };
            return self.unbox_whole(ty, native, value);
        }
        match (native, formal, value) {
            (Shape::Leaf(actual), Shape::Leaf(expected), Val::Leaf(value))
                if actual == expected && value.sort() == actual.sort() =>
            {
                Ok(Val::Leaf(value))
            }
            (Shape::Node(actual), Shape::Node(expected), Val::Node(values))
                if actual.len() == expected.len() && actual.len() == values.len() =>
            {
                let layout = self.layout(ty, false)?;
                if layout.children.len() != actual.len() {
                    return Err(refusal(
                        "generic-product",
                        "a formal structural product has another arity",
                        self.span,
                    ));
                }
                let mut fields = Vec::new();
                for (((ty, native), formal), value) in
                    layout.children.iter().zip(actual).zip(expected).zip(values)
                {
                    fields.push(self.convert(ty, native, formal, value, boxing)?);
                }
                Ok(Val::Node(fields))
            }
            _ => Err(refusal(
                "generic-product",
                "incompatible source-formal and actual product layouts",
                self.span,
            )),
        }
    }
}

impl Ctx<'_> {
    pub(super) fn box_native_value(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        value: Val,
        span: SpanId,
    ) -> Result<Term, VcRefusal> {
        let shape = self.shape(ty, env.owner(), span)?;
        let mut codec = Codec {
            ctx: self,
            caller: env,
            callee: env,
            span,
            left: 1024,
        };
        codec.box_whole(ty, &shape, value)
    }

    pub(super) fn unbox_native_value(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        value: Term,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        let shape = self.shape(ty, env.owner(), span)?;
        let mut codec = Codec {
            ctx: self,
            caller: env,
            callee: env,
            span,
            left: 1024,
        };
        codec.unbox_whole(ty, &shape, value)
    }

    pub(crate) fn formal_value(
        &self,
        view: FormalValue<'_>,
        shape: &Shape,
        value: Val,
    ) -> Result<Val, VcRefusal> {
        let boxing = !matches!(view.position, FormalPosition::Result);
        let callee = view
            .callee
            .owner()
            .and_then(|id| self.fns.get(&id))
            .ok_or_else(|| {
                refusal(
                    "generic-product",
                    "a formal conversion without its actual source declaration",
                    view.span,
                )
            })?;
        let formal_ty = match view.position {
            FormalPosition::SpecParameter(index) | FormalPosition::NativeParameter(index) => callee
                .params
                .get(index)
                .and_then(|local| callee.local(*local))
                .map(|local| &local.ty),
            FormalPosition::Result => callee.ret_ty(),
        }
        .ok_or_else(|| {
            refusal(
                "generic-product",
                "a formal conversion outside the source signature",
                view.span,
            )
        })?;
        if callee.type_params.len() != view.type_args.len()
            || view.callee.len() != view.type_args.len()
            || formal_ty.subst(view.type_args) != *view.actual_ty
        {
            return Err(refusal(
                "generic-product",
                "source-formal substitution differs from the actual type",
                view.span,
            ));
        }
        let expected = match view.position {
            FormalPosition::SpecParameter(_) if !callee.type_params.is_empty() => {
                self.poly_shape(formal_ty, Some(callee.id), view.span)?
            }
            _ => self.shape(formal_ty, Some(callee.id), view.span)?,
        };
        if *shape != expected {
            return Err(refusal(
                "generic-product",
                "a formal ABI layout differs from its source signature",
                view.span,
            ));
        }
        let native = self.shape(view.actual_ty, view.caller.owner(), view.span)?;
        let mut codec = Codec {
            ctx: self,
            caller: view.caller,
            callee: view.callee,
            span: view.span,
            left: 1024,
        };
        for (index, ty) in view.type_args.iter().enumerate() {
            let index = u32::try_from(index).map_err(|_| {
                refusal(
                    "generic-product",
                    "a callee type-vector index exceeds its representation",
                    view.span,
                )
            })?;
            if view.callee.get(index) != Some(&codec.actual_type(ty)?) {
                return Err(refusal(
                    "generic-product",
                    "the complete callee type vector differs from its source substitution",
                    view.span,
                ));
            }
        }
        if !shape.has_poly() && *shape == native && value.matches(shape) {
            return Ok(value);
        }
        codec.convert(view.actual_ty, &native, shape, value, boxing)
    }
}

#[cfg(test)]
mod tests;
