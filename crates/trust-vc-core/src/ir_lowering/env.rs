//! Lowering environment metadata and type registration.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use crate::encoder::datatype::{selector_symbol_name, tester_symbol_name, variant_symbol_name};
use crate::ir::{DatatypeVariant, TrustVcType};
use crate::ir_expr::TrustVcExpr;
use quote::quote;

use super::LoweringError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FieldMeta {
    pub(crate) uf_name: String,
    pub(crate) field_type: TrustVcType,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MethodMeta {
    pub(crate) uf_name: String,
    pub(crate) return_type: TrustVcType,
    pub(crate) param_types: Vec<TrustVcType>,
    /// Box function name (`Box_T`) to lift a CONCRETE receiver into the
    /// type-erased `Poly` sort before applying `uf_name`, or `None` to pass the
    /// receiver bare.
    ///
    /// `None` is the generic/default path: a generic receiver `t: T` (or a
    /// datatype-accessor receiver) is already in the sort `uf_name` expects, so
    /// it passes unchanged — this preserves the existing behavior byte-for-byte.
    ///
    /// `Some("Box_T")` is set ONLY for concrete-impl trait-method registrations
    /// (Slice 1 of #33): the trait UF `Trait__method` has a `Poly` self-domain,
    /// so a concrete receiver `s: S` must be wrapped `Trait__method(Box_S(s), …)`
    /// to (a) sort-check and (b) match the per-impl linking-axiom trigger shape
    /// `{Trait__method(Box_S(self), …)}`. The value then comes ONLY from the
    /// trait's declared postcondition axiom (contract), never the impl body.
    pub(crate) box_receiver: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConstructorMeta {
    pub(crate) uf_name: String,
    pub(crate) fields: Vec<(String, TrustVcType)>,
}

/// Per-variant metadata for multi-variant datatypes, keyed by bare variant name.
///
/// Allows expression lowering to resolve constructor paths like `None`,
/// `Some(x)`, `Ok(v)`, or `Err(e)` to the correct UF name and return type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DatatypeVariantMeta {
    pub(crate) datatype_name: String,
    pub(crate) variant_name: String,
    pub(crate) uf_name: String,
    pub(crate) fields: Vec<(String, TrustVcType)>,
    pub(crate) return_ty: TrustVcType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub(crate) enum OptionBindingState {
    Some { value: Option<TrustVcExpr> },
    None,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OptionBindingMeta {
    pub(crate) ty: TrustVcType,
    pub(crate) state: OptionBindingState,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub(crate) enum ResultBindingState {
    Ok { value: Option<TrustVcExpr> },
    Err { error: Option<TrustVcExpr> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResultBindingMeta {
    pub(crate) ty: TrustVcType,
    pub(crate) state: ResultBindingState,
}

pub(crate) const COLLECTION_CONSTRUCTOR_PREFIX: &str = "__trust_vc_collection_ctor_";
pub(crate) const SEQ_FROM_FN_BUILTIN: &str = "__trust_vc_seq_from_fn";
/// `__trust_vc_let_bound::<T>(value)`: a body `let v: T = value;` as the
/// extractor substitutes it, lowered as `value` bound at `T` (§5b rule 6).
pub(crate) const LET_BOUND_MARKER: &str = "__trust_vc_let_bound";
/// `__trust_vc_bind_like(witness, value)`: a value the extractor writes into a
/// slot with no written type (an unascribed binding, a pattern binding, a
/// field), lowered as `value` bound at the type `witness` derives (§5b rule
/// 12).
pub(crate) const BIND_LIKE_MARKER: &str = "__trust_vc_bind_like";
/// `__trust_vc_self_typed(value)`: an argument substituted for a closure
/// parameter whose type is neither written (`|a: T|`) nor declared by the
/// closure's binding. Rust gives that parameter one type, unified from every
/// call of the closure and every use in its body; the lowering reads only the
/// argument, so the argument must carry its type itself. It is lowered as
/// `value`, and REFUSED when `value` is an untyped literal form (an unsuffixed
/// integer or float literal, or a name bound to one) whose type only its
/// context fixes (§5b rule 11).
pub(crate) const SELF_TYPED_MARKER: &str = "__trust_vc_self_typed";
/// `__trust_vc_untyped_site(value)`: the value of an exec arithmetic-safety
/// site whose slot type the obligation does not hold. Lowered as `value`,
/// and REFUSED when `value` is a constant untyped literal form that panics in
/// a fixed-width type it may take (`untyped_site.rs`).
pub(crate) const UNTYPED_SITE_MARKER: &str = "__trust_vc_untyped_site";
/// `__trust_vc_untyped_binding(value)`: the value of an unascribed `let` of an
/// untyped literal form whose type the binding's uses do not determine here.
/// Lowered as a conditional with one value (`untyped_site.rs`): wherever it
/// meets no peer it is checked in every type it may take, and a constant one
/// that panics in such a type is refused.
pub(crate) const UNTYPED_BINDING_MARKER: &str = "__trust_vc_untyped_binding";
/// `__trust_vc_slot_typed::<T>(value)`: the value of an exec arithmetic-safety
/// site that fills a slot of type `T` (a parameter, an inferred binding): an
/// untyped literal form there is typed at `T` (refused when a literal does
/// not fit it); a value of its own type is left as it is (`untyped_site.rs`).
pub(crate) const SLOT_TYPED_MARKER: &str = "__trust_vc_slot_typed";
pub(crate) const SET_NEW_BUILTIN: &str = "__trust_vc_set_new";

/// Type environment for variable and function return type lookups during lowering.
///
/// Separates variable types from function return types to prevent name collisions
/// where a variable and function share the same name. Fixes #2235.
#[derive(Debug, Clone)]
pub(crate) struct TypeEnv {
    vars: HashMap<String, TrustVcType>,
    type_aliases: HashMap<String, TrustVcType>,
    /// Bare names declared by the source type registry. This provenance is
    /// separate from the lowered datatype carrier: a user `enum Option<T>` can
    /// have the exact same name/variants as std::Option while defining custom
    /// PartialEq/Clone semantics.
    source_type_names: HashSet<String>,
    erased_shared_ref_vars: HashSet<String>,
    erased_ghost_vars: HashSet<String>,
    prophecy_bindings: HashMap<String, TrustVcType>,
    fn_return_types: HashMap<String, TrustVcType>,
    fn_param_types: HashMap<String, Vec<TrustVcType>>,
    /// H10: declaration-order type/const generic parameter names of a function
    /// whose registration checked generic carriage. Cleared whenever the
    /// function's parameter types are re-registered.
    fn_generic_params: HashMap<String, Vec<String>>,
    field_metadata: HashMap<String, HashMap<String, FieldMeta>>,
    method_metadata: HashMap<(String, String), MethodMeta>,
    /// H10 (method half): declaration-order type/const generic parameter names
    /// of a registered METHOD's own signature (`fn k<P>(&self)` → `["P"]`),
    /// keyed exactly like [`Self::method_metadata`]. Recorded only by a
    /// registration that carries the declaration's generics; cleared whenever
    /// the method's metadata is re-registered, so a stale list can never
    /// describe a different signature.
    ///
    /// ABSENT is not "non-generic": it means the registration recorded nothing,
    /// and the call site treats an explicit turbofish over such a method as
    /// unmappable and fails closed.
    method_generic_params: HashMap<(String, String), Vec<String>>,
    /// `(datatype_name, method_name)` pairs whose `method_metadata` entry was
    /// synthesized by [`Self::register_variant_helper_methods`] — i.e. the
    /// auto-generated datatype tester (`is_V`) / selector (`get_V_field`)
    /// accessors. Tracked so that a user-written inherent method whose name
    /// coincides with a datatype accessor (e.g. a hand-written `fn is_A(&self)`
    /// / `fn get_A_0(&self)`) is reconciled against the canonical accessor
    /// instead of being rejected as conflicting metadata. See
    /// [`prepared_context::type_env::register_method_metadata`].
    auto_accessor_methods: HashSet<(String, String)>,
    constructor_metadata: HashMap<String, ConstructorMeta>,
    option_bindings: HashMap<String, OptionBindingMeta>,
    result_bindings: HashMap<String, ResultBindingMeta>,
    /// Per-variant constructor metadata indexed by bare variant name.
    /// Multiple datatypes may expose variants with the same name.
    variant_metadata: HashMap<String, Vec<DatatypeVariantMeta>>,
    /// Datatype names whose source carried `#[derive(PartialEq)]` — their `==` /
    /// `.eq()` is the STRUCTURAL field-wise equality, so (with structural fields)
    /// `x.eq(&y)` may lower to `x == y`. Absent ⇒ a possibly-custom `PartialEq`.
    derived_partial_eq_types: HashSet<String>,
    /// Datatype names whose source carried `#[derive(Clone)]` — `.clone()` is then
    /// the structural value copy (`x.clone() == x`).
    derived_clone_types: HashSet<String>,
    /// Datatype names with a hand-written `impl PartialEq` in source (NOT a
    /// `#[derive(PartialEq)]`). Such a type's EXEC `==` calls that custom impl,
    /// which may be non-structural (e.g. `fn eq(..) -> bool { false }`), so
    /// structural-lowering its `==` operator would be a false-verify. Used to
    /// fail-close the `==`/`!=` operator on these types (and any datatype that
    /// transitively contains one as a field). Spec-only extensional `==` is a
    /// separate concern; this conservative gate matches the `.eq()` method gate.
    manual_partial_eq_types: HashSet<String>,
    /// Crate-private capability for the synthetic source-catalog `int` result
    /// marker. False in every ordinary/user-authored lowering environment.
    allow_source_catalog_math_int_marker: bool,
    /// The operator methods (`add`, `shl`, `shr`) that are the std operator on
    /// a primitive integer receiver here, because the std trait is in scope at
    /// every call of them in the source file. Empty unless the extractor
    /// showed it, so a call of one of them on an integer is refused.
    std_operator_methods: HashSet<String>,
}

impl TypeEnv {
    pub fn new() -> Self {
        TypeEnv {
            vars: HashMap::new(),
            type_aliases: HashMap::new(),
            source_type_names: HashSet::new(),
            erased_shared_ref_vars: HashSet::new(),
            erased_ghost_vars: HashSet::new(),
            prophecy_bindings: HashMap::new(),
            fn_return_types: HashMap::new(),
            fn_param_types: HashMap::new(),
            fn_generic_params: HashMap::new(),
            field_metadata: HashMap::new(),
            method_metadata: HashMap::new(),
            method_generic_params: HashMap::new(),
            auto_accessor_methods: HashSet::new(),
            constructor_metadata: HashMap::new(),
            option_bindings: HashMap::new(),
            result_bindings: HashMap::new(),
            variant_metadata: HashMap::new(),
            derived_partial_eq_types: HashSet::new(),
            derived_clone_types: HashSet::new(),
            manual_partial_eq_types: HashSet::new(),
            allow_source_catalog_math_int_marker: false,
            std_operator_methods: HashSet::new(),
        }
    }

    /// Returns a scoped clone that may consume the synthetic source-catalog
    /// mathematical-integer result marker. The original environment remains
    /// incapable, so the permission cannot leak to another obligation.
    pub(crate) fn with_source_catalog_math_int_marker(mut self) -> Self {
        self.allow_source_catalog_math_int_marker = true;
        self
    }

    /// Whether this exact scoped environment carries the internal marker
    /// capability. There is intentionally no public or mutable setter.
    pub(crate) const fn allows_source_catalog_math_int_marker(&self) -> bool {
        self.allow_source_catalog_math_int_marker
    }

    /// Records that `method` (`add`, `shl` or `shr`) on a primitive integer is
    /// the std operator method in this environment's source.
    pub(crate) fn register_std_operator_method(&mut self, method: impl Into<String>) {
        self.std_operator_methods.insert(method.into());
    }

    /// Whether `method` on a primitive integer is the std operator method.
    #[must_use]
    pub(crate) fn reads_std_operator_method(&self, method: &str) -> bool {
        self.std_operator_methods.contains(method)
    }

    /// Records that a datatype's source carried `#[derive(PartialEq)]`.
    pub fn register_derived_partial_eq(&mut self, name: impl Into<String>) {
        self.derived_partial_eq_types.insert(name.into());
    }

    /// Records that a datatype's source carried `#[derive(Clone)]`.
    pub fn register_derived_clone(&mut self, name: impl Into<String>) {
        self.derived_clone_types.insert(name.into());
    }

    /// Records that a datatype has a hand-written `impl PartialEq` in source.
    pub fn register_manual_partial_eq(&mut self, name: impl Into<String>) {
        self.manual_partial_eq_types.insert(name.into());
    }

    /// Whether `name` has a hand-written (non-derived) `impl PartialEq`.
    #[must_use]
    pub fn has_manual_partial_eq(&self, name: &str) -> bool {
        self.manual_partial_eq_types.contains(name)
    }

    /// Whether `name` carried `#[derive(PartialEq)]` (structural equality).
    #[must_use]
    pub fn has_derived_partial_eq(&self, name: &str) -> bool {
        self.derived_partial_eq_types.contains(name)
    }

    /// Whether `name` carried `#[derive(Clone)]` (structural clone).
    #[must_use]
    pub fn has_derived_clone(&self, name: &str) -> bool {
        self.derived_clone_types.contains(name)
    }

    pub fn lookup(&self, name: &str) -> Option<&TrustVcType> {
        self.vars.get(name)
    }

    pub fn insert(&mut self, name: String, ty: TrustVcType) {
        self.register_type_metadata(&ty);
        self.prophecy_bindings.remove(&name);
        self.option_bindings.remove(&name);
        self.result_bindings.remove(&name);
        self.vars.insert(name, ty);
    }

    pub(crate) fn insert_type_alias(&mut self, name: String, ty: TrustVcType) {
        self.record_source_type_name(&name);
        self.register_type_metadata(&ty);
        self.type_aliases.insert(name, ty);
    }

    /// Inserts a type alias WITHOUT registering datatype variant metadata.
    ///
    /// Used for generic enum TEMPLATE carriers (`GList`, whose `GCons` field is a
    /// `TypeParam`): the template is kept as a type alias for resolution, but its
    /// variant metadata must NOT be registered — it would compete with the real
    /// per-instantiation carrier `GList<i32>` (both share the base name `GList`)
    /// and make every `GList::GCons` constructor path ambiguous. Only concrete
    /// monomorphized instantiations register usable constructor/selector metadata.
    pub(crate) fn insert_type_alias_without_metadata(&mut self, name: String, ty: TrustVcType) {
        self.record_source_type_name(&name);
        self.type_aliases.insert(name, ty);
    }

    fn record_source_type_name(&mut self, name: &str) {
        let bare = name.split('<').next().unwrap_or(name).trim();
        if !bare.is_empty() {
            self.source_type_names.insert(bare.to_string());
        }
    }

    pub(crate) fn source_type_shadows_builtin(&self, name: &str) -> bool {
        self.source_type_names.contains(name)
    }

    pub(crate) fn lookup_type_alias(&self, name: &str) -> Option<&TrustVcType> {
        self.type_aliases.get(name)
    }

    pub(crate) fn resolve_syn_type(&self, ty: &syn::Type) -> Result<TrustVcType, LoweringError> {
        self.resolve_syn_type_inner(ty, &mut HashSet::new())
    }

    fn resolve_syn_type_inner(
        &self,
        ty: &syn::Type,
        seen_aliases: &mut HashSet<String>,
    ) -> Result<TrustVcType, LoweringError> {
        if let syn::Type::Reference(reference) = ty {
            return self.resolve_syn_type_inner(&reference.elem, seen_aliases);
        }
        if let syn::Type::Path(type_path) = ty {
            if let Some(result_ty) = self.resolve_result_type_path(type_path, seen_aliases)? {
                return Ok(result_ty);
            }
            if type_path.qself.is_none() && type_path.path.segments.len() == 1 {
                let segment = &type_path.path.segments[0];
                if matches!(segment.arguments, syn::PathArguments::None) {
                    let name = segment.ident.to_string();
                    if let Some(alias_ty) = self.lookup_type_alias(&name) {
                        if !seen_aliases.insert(name.clone()) {
                            return Err(LoweringError::InvalidType(format!(
                                "cycle detected while resolving type alias '{}'",
                                name
                            )));
                        }
                        let resolved = alias_ty.clone();
                        seen_aliases.remove(&name);
                        return Ok(resolved);
                    }
                    if let Some(struct_ty) = self.registered_single_variant_type(&name) {
                        return Ok(struct_ty);
                    }
                }
            }
        }
        let rendered = self.render_syn_type_with_aliases(ty, seen_aliases)?;
        Ok(TrustVcType::parse_or_opaque(&rendered))
    }

    fn resolve_result_type_path(
        &self,
        type_path: &syn::TypePath,
        seen_aliases: &mut HashSet<String>,
    ) -> Result<Option<TrustVcType>, LoweringError> {
        if type_path.qself.is_some() {
            return Ok(None);
        }
        let Some(segment) = type_path.path.segments.last() else {
            return Ok(None);
        };
        if segment.ident != "Result" {
            return Ok(None);
        }
        let syn::PathArguments::AngleBracketed(args) = &segment.arguments else {
            return Ok(None);
        };
        let mut type_args = args.args.iter().filter_map(|arg| match arg {
            syn::GenericArgument::Type(ty) => Some(ty),
            _ => None,
        });
        let ok_syn_ty = type_args.next().ok_or_else(|| {
            LoweringError::TypeInference("Result type is missing its Ok type argument".to_string())
        })?;
        let err_syn_ty = type_args.next().ok_or_else(|| {
            LoweringError::TypeInference("Result type is missing its Err type argument".to_string())
        })?;
        if type_args.next().is_some() {
            return Err(LoweringError::TypeInference(
                "Result type expects exactly 2 type arguments".to_string(),
            ));
        }
        let ok_ty = self.resolve_syn_type_inner(ok_syn_ty, seen_aliases)?;
        let err_ty = self.resolve_syn_type_inner(err_syn_ty, seen_aliases)?;
        Ok(Some(result_type(ok_ty, err_ty)))
    }

    fn registered_single_variant_type(&self, name: &str) -> Option<TrustVcType> {
        let meta = self.lookup_constructor(name)?;
        Some(TrustVcType::Datatype {
            name: name.to_string(),
            variants: vec![DatatypeVariant::new(name, meta.fields.clone())],
        })
    }

    fn render_syn_type_with_aliases(
        &self,
        ty: &syn::Type,
        seen_aliases: &mut HashSet<String>,
    ) -> Result<String, LoweringError> {
        match ty {
            syn::Type::Reference(reference) => {
                self.render_syn_type_with_aliases(&reference.elem, seen_aliases)
            }
            syn::Type::Path(type_path) if type_path.qself.is_none() => Ok(type_path
                .path
                .segments
                .iter()
                .map(|segment| {
                    let ident = segment.ident.to_string();
                    match &segment.arguments {
                        syn::PathArguments::None => {
                            if let Some(alias_ty) = self.lookup_type_alias(&ident) {
                                Ok(alias_ty.to_type_string())
                            } else {
                                Ok(ident)
                            }
                        }
                        syn::PathArguments::AngleBracketed(args) => {
                            let rendered_args = args
                                .args
                                .iter()
                                .map(|arg| match arg {
                                    syn::GenericArgument::Type(ty) => self
                                        .resolve_syn_type_inner(ty, seen_aliases)
                                        .map(|ty| ty.to_type_string()),
                                    _ => Ok(quote!(#arg).to_string().replace(' ', "")),
                                })
                                .collect::<Result<Vec<_>, LoweringError>>()?
                                .join(", ");
                            Ok(format!("{ident}<{rendered_args}>"))
                        }
                        syn::PathArguments::Parenthesized(_) => Ok(ident),
                    }
                })
                .collect::<Result<Vec<_>, LoweringError>>()?
                .join("::")),
            _ => Ok(quote!(#ty).to_string().replace(' ', "")),
        }
    }

    pub(crate) fn insert_erased_shared_ref_var(&mut self, name: String) {
        self.erased_shared_ref_vars.insert(name);
    }

    pub(crate) fn is_erased_shared_ref_var(&self, name: &str) -> bool {
        self.erased_shared_ref_vars.contains(name)
    }

    pub(crate) fn insert_erased_ghost_var(&mut self, name: String) {
        self.erased_ghost_vars.insert(name);
    }

    pub(crate) fn is_erased_ghost_var(&self, name: &str) -> bool {
        self.erased_ghost_vars.contains(name)
    }

    pub(crate) fn register_type_metadata_only(&mut self, ty: &TrustVcType) {
        self.register_type_metadata(ty);
    }

    pub(crate) fn insert_option_binding(&mut self, name: String, meta: OptionBindingMeta) {
        self.option_bindings.insert(name, meta);
    }

    pub(crate) fn lookup_option_binding(&self, name: &str) -> Option<&OptionBindingMeta> {
        self.option_bindings.get(name)
    }

    pub(crate) fn insert_result_binding(&mut self, name: String, meta: ResultBindingMeta) {
        self.result_bindings.insert(name, meta);
    }

    pub(crate) fn lookup_result_binding(&self, name: &str) -> Option<&ResultBindingMeta> {
        self.result_bindings.get(name)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn insert_prophecy_binding(&mut self, name: String, ty: TrustVcType) {
        self.prophecy_bindings.insert(name, ty);
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn lookup_prophecy(&self, name: &str) -> Option<&TrustVcType> {
        self.prophecy_bindings.get(name)
    }

    pub fn lookup_fn(&self, name: &str) -> Option<&TrustVcType> {
        self.fn_return_types.get(name)
    }

    pub fn insert_fn(&mut self, name: String, return_ty: TrustVcType) {
        self.register_type_metadata(&return_ty);
        self.fn_return_types.insert(name, return_ty);
    }

    pub fn lookup_fn_params(&self, name: &str) -> Option<&[TrustVcType]> {
        self.fn_param_types.get(name).map(Vec::as_slice)
    }

    pub fn insert_fn_params(&mut self, name: String, param_types: Vec<TrustVcType>) {
        for param_type in &param_types {
            self.register_type_metadata(param_type);
        }
        self.fn_generic_params.remove(&name);
        self.fn_param_types.insert(name, param_types);
    }

    /// H10: the declaration-order generic parameter names of `name`, when its
    /// registration recorded them (see `insert_fn_generic_params`).
    pub(crate) fn lookup_fn_generic_params(&self, name: &str) -> Option<&[String]> {
        self.fn_generic_params.get(name).map(Vec::as_slice)
    }

    /// H10: record the declaration-order generic parameter names of a function
    /// whose parameter types are already registered.
    pub(crate) fn insert_fn_generic_params(&mut self, name: String, generic_params: Vec<String>) {
        if self.fn_param_types.contains_key(&name) {
            self.fn_generic_params.insert(name, generic_params);
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn insert_field_metadata(
        &mut self,
        type_name: String,
        field_name: String,
        uf_name: String,
        field_type: TrustVcType,
    ) {
        self.field_metadata.entry(type_name).or_default().insert(
            field_name,
            FieldMeta {
                uf_name,
                field_type,
            },
        );
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn lookup_field(&self, type_name: &str, field_name: &str) -> Option<&FieldMeta> {
        self.field_metadata.get(type_name)?.get(field_name)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn insert_method_metadata(
        &mut self,
        receiver_type_name: String,
        method_name: String,
        meta: MethodMeta,
    ) {
        self.method_generic_params
            .remove(&(receiver_type_name.clone(), method_name.clone()));
        self.method_metadata
            .insert((receiver_type_name, method_name), meta);
    }

    /// H10 (method half): record the declaration-order generic parameter names
    /// of a method whose metadata is already registered. A method with no
    /// metadata records nothing, so the pair can never describe a signature the
    /// lowering does not have.
    pub(crate) fn insert_method_generic_params(
        &mut self,
        receiver_type_name: String,
        method_name: String,
        generic_params: Vec<String>,
    ) {
        let key = (receiver_type_name, method_name);
        if self.method_metadata.contains_key(&key) {
            self.method_generic_params.insert(key, generic_params);
        }
    }

    /// H10 (method half): the recorded declaration-order generic parameter
    /// names of `(receiver_type_name, method_name)`, or `None` when the
    /// registration recorded none.
    pub(crate) fn lookup_method_generic_params(
        &self,
        receiver_type_name: &str,
        method_name: &str,
    ) -> Option<&[String]> {
        self.method_generic_params
            .get(&(receiver_type_name.to_string(), method_name.to_string()))
            .map(Vec::as_slice)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn lookup_method(
        &self,
        receiver_type_name: &str,
        method_name: &str,
    ) -> Option<&MethodMeta> {
        self.method_metadata
            .get(&(receiver_type_name.to_string(), method_name.to_string()))
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn insert_constructor_metadata(&mut self, type_name: String, meta: ConstructorMeta) {
        self.constructor_metadata.insert(type_name, meta);
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn lookup_constructor(&self, type_name: &str) -> Option<&ConstructorMeta> {
        self.constructor_metadata.get(type_name)
    }

    /// Look up variant metadata by bare variant name.
    ///
    /// Returns all registered variants with that name (may come from different
    /// datatypes). Returns `None` if no datatype has a variant with that name.
    pub(crate) fn lookup_variants(&self, variant_name: &str) -> Option<&[DatatypeVariantMeta]> {
        self.variant_metadata.get(variant_name).map(Vec::as_slice)
    }

    /// Resolve a constructor path to a unique variant.
    ///
    /// - Single-segment path (`None`): unique among all registered datatypes.
    /// - Qualified path (`Option::None`): uses the penultimate segment as a
    ///   datatype base-name hint to disambiguate.
    ///
    /// Returns `Ok(None)` if the path doesn't match any variant,
    /// `Err` if it matches ambiguously.
    #[allow(clippy::indexing_slicing)] // candidates[0]/filtered[0] are only used in len() == 1 branches; dt_names[0] is only used after candidates.len() > 1; segments[len()-2] only runs for qualified paths
    pub(crate) fn resolve_variant_constructor(
        &self,
        path: &syn::Path,
    ) -> Result<Option<&DatatypeVariantMeta>, LoweringError> {
        let segments: Vec<_> = path.segments.iter().map(|s| s.ident.to_string()).collect();
        let Some(variant_name) = segments.last() else {
            return Ok(None);
        };
        let candidates = match self.lookup_variants(variant_name) {
            Some(c) if !c.is_empty() => c,
            _ => return Ok(None),
        };

        if segments.len() == 1 {
            if candidates.len() == 1 {
                return Ok(Some(&candidates[0]));
            }
            let dt_names: Vec<_> = candidates
                .iter()
                .map(|c| c.datatype_name.as_str())
                .collect();
            return Err(LoweringError::TypeInference(format!(
                "ambiguous constructor '{}': matches datatypes {}; use a qualified path like {}::{}",
                variant_name,
                dt_names.join(", "),
                dt_names[0],
                variant_name,
            )));
        }

        let qualifier = &segments[segments.len() - 2];
        let filtered: Vec<_> = candidates
            .iter()
            .filter(|c| {
                let base = c
                    .datatype_name
                    .split('<')
                    .next()
                    .unwrap_or(&c.datatype_name);
                base == qualifier
            })
            .collect();

        match filtered.len() {
            0 => Ok(None),
            1 => Ok(Some(filtered[0])),
            _ => {
                let dt_names: Vec<_> = filtered.iter().map(|c| c.datatype_name.as_str()).collect();
                Err(LoweringError::TypeInference(format!(
                    "ambiguous qualified constructor '{}::{}': matches {}",
                    qualifier,
                    variant_name,
                    dt_names.join(", "),
                )))
            }
        }
    }

    pub fn extend(&self, bindings: &[(String, TrustVcType)]) -> Self {
        let mut child = self.clone();
        for (name, ty) in bindings {
            child.insert(name.clone(), ty.clone());
        }
        child
    }

    fn register_type_metadata(&mut self, ty: &TrustVcType) {
        let mut seen = HashSet::new();
        self.register_type_metadata_inner(ty, &mut seen);
    }

    fn register_type_metadata_inner(&mut self, ty: &TrustVcType, seen: &mut HashSet<String>) {
        match ty {
            TrustVcType::Seq(inner)
            | TrustVcType::Array(inner, _)
            | TrustVcType::Set(inner)
            | TrustVcType::Multiset(inner) => self.register_type_metadata_inner(inner, seen),
            TrustVcType::Map(key, value) => {
                self.register_type_metadata_inner(key, seen);
                self.register_type_metadata_inner(value, seen);
            }
            TrustVcType::SpecFn(args, ret) => {
                for arg in args {
                    self.register_type_metadata_inner(arg, seen);
                }
                self.register_type_metadata_inner(ret, seen);
            }
            TrustVcType::RecursiveRef(_) => {}
            TrustVcType::Datatype { name, variants } => {
                if !seen.insert(name.clone()) {
                    return;
                }
                for variant in variants {
                    for (_, field_type) in &variant.fields {
                        self.register_type_metadata_inner(field_type, seen);
                    }
                }
                self.register_all_variant_metadata(name, ty, variants);
                if let [variant] = variants.as_slice() {
                    self.register_single_variant_metadata(name, variant);
                }
            }
            _ => {}
        }
    }

    fn register_single_variant_metadata(&mut self, datatype_name: &str, variant: &DatatypeVariant) {
        self.field_metadata
            .entry(datatype_name.to_string())
            .or_insert_with(|| {
                variant
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(index, (field_name, field_type))| {
                        (
                            field_name.clone(),
                            FieldMeta {
                                uf_name: selector_symbol_name(
                                    datatype_name,
                                    &variant.name,
                                    field_name,
                                    index,
                                ),
                                field_type: field_type.clone(),
                            },
                        )
                    })
                    .collect()
            });
        self.constructor_metadata
            .entry(datatype_name.to_string())
            .or_insert_with(|| ConstructorMeta {
                uf_name: variant_symbol_name(datatype_name, &variant.name),
                fields: variant.fields.clone(),
            });
    }

    fn register_all_variant_metadata(
        &mut self,
        datatype_name: &str,
        datatype_ty: &TrustVcType,
        variants: &[DatatypeVariant],
    ) {
        for variant in variants {
            self.register_variant_helper_methods(datatype_name, variant);
            let meta = DatatypeVariantMeta {
                datatype_name: datatype_name.to_string(),
                variant_name: variant.name.clone(),
                uf_name: variant_symbol_name(datatype_name, &variant.name),
                fields: variant.fields.clone(),
                return_ty: datatype_ty.clone(),
            };
            let variants = self
                .variant_metadata
                .entry(variant.name.clone())
                .or_default();
            if !variants.iter().any(|existing| existing == &meta) {
                variants.push(meta);
            }
        }
    }

    fn register_variant_helper_methods(&mut self, datatype_name: &str, variant: &DatatypeVariant) {
        let tester_key = (datatype_name.to_string(), format!("is_{}", variant.name));
        self.method_metadata
            .entry(tester_key.clone())
            .or_insert_with(|| MethodMeta {
                uf_name: tester_symbol_name(datatype_name, &variant.name),
                return_type: TrustVcType::Bool,
                param_types: vec![],
                box_receiver: None,
            });
        self.auto_accessor_methods.insert(tester_key);

        for (index, (field_name, field_type)) in variant.fields.iter().enumerate() {
            let selector_key = (
                datatype_name.to_string(),
                format!("get_{}_{}", variant.name, field_name),
            );
            self.method_metadata
                .entry(selector_key.clone())
                .or_insert_with(|| MethodMeta {
                    uf_name: selector_symbol_name(datatype_name, &variant.name, field_name, index),
                    return_type: field_type.clone(),
                    param_types: vec![],
                    box_receiver: None,
                });
            self.auto_accessor_methods.insert(selector_key);
        }
    }

    /// True when `(receiver_type_name, method_name)` names an auto-generated
    /// datatype accessor (a variant tester `is_V` or field selector
    /// `get_V_field`) synthesized by [`Self::register_variant_helper_methods`].
    ///
    /// Used by type-environment construction to reconcile a user-written
    /// inherent method that shadows a datatype accessor's name: the canonical,
    /// encoder-backed accessor is authoritative (it carries the true selector /
    /// tester semantics), so the user re-declaration is folded into it rather
    /// than rejected as a metadata conflict. Keeping the accessor only ever adds
    /// true datatype facts, so this is sound (it never turns a real obligation
    /// into a false pass).
    pub(crate) fn is_auto_accessor_method(
        &self,
        receiver_type_name: &str,
        method_name: &str,
    ) -> bool {
        self.auto_accessor_methods
            .contains(&(receiver_type_name.to_string(), method_name.to_string()))
    }
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

fn result_type(ok_ty: TrustVcType, err_ty: TrustVcType) -> TrustVcType {
    TrustVcType::Datatype {
        name: format!(
            "Result<{}, {}>",
            ok_ty.to_type_string(),
            err_ty.to_type_string()
        ),
        variants: vec![
            DatatypeVariant::new("Ok", vec![("0".to_string(), ok_ty)]),
            DatatypeVariant::new("Err", vec![("0".to_string(), err_ty)]),
        ],
    }
}
