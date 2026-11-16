//! Opaque reference operations through the crate's boxed value ABI.
use super::*;

impl Ctx<'_> {
    pub(crate) fn mut_ref_projection(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        reference: Val,
        future: bool,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        let Ty::MutRef(inner) = ty else {
            return Err(refusal(
                "mut-ref-type",
                "projection of a non-reference",
                span,
            ));
        };
        // Register the complete decorated referent identity before emitting
        // its projection's membership axioms.
        self.type_argument(ty, env, span)?;
        let Val::Leaf(reference) = reference else {
            return Err(refusal(
                "mut-ref-type",
                "a reference without opaque identity",
                span,
            ));
        };
        let value = self
            .types
            .borrow_mut()
            .mut_ref_projection(reference, future)
            .ok_or_else(|| {
                refusal(
                    "mut-ref-type",
                    "a reference projection with incompatible sort",
                    span,
                )
            })?;
        self.unbox_native_value(inner, env, value, span)
    }

    pub(crate) fn mut_ref_update(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        reference: Val,
        value: Val,
        span: SpanId,
    ) -> Result<Val, VcRefusal> {
        let Ty::MutRef(inner) = ty else {
            return Err(refusal("mut-ref-type", "update of a non-reference", span));
        };
        self.type_argument(ty, env, span)?;
        let Val::Leaf(reference) = reference else {
            return Err(refusal(
                "mut-ref-type",
                "a reference without opaque identity",
                span,
            ));
        };
        let value = self.box_native_value(inner, env, value, span)?;
        self.types
            .borrow_mut()
            .mut_ref_update(reference, value)
            .map(Val::Leaf)
            .ok_or_else(|| {
                refusal(
                    "mut-ref-type",
                    "a reference update with incompatible sorts",
                    span,
                )
            })
    }

    pub(crate) fn has_resolved(
        &self,
        ty: &Ty,
        env: &TypeEnv,
        value: Val,
        span: SpanId,
    ) -> Result<Term, VcRefusal> {
        let argument = self.type_argument(ty, env, span)?;
        let value = self.box_native_value(ty, env, value, span)?;
        self.types
            .borrow_mut()
            .has_resolved(argument, value)
            .ok_or_else(|| {
                refusal(
                    "resolution-type",
                    "a resolution predicate with incompatible sort",
                    span,
                )
            })
    }
}
