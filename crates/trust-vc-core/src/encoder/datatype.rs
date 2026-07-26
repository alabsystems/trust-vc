//! Native-datatype encoding support for builtin datatypes such as `Option<T>`
//! and `Result<T, E>`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `register_datatype` declares each datatype with ay's native datatype theory
//! (`Solver::try_declare_datatype`) over the carrier sort
//! `Sort::Uninterpreted(name)` (ay's term-level form of `Sort::Datatype`), and
//! exposes constructor/selector/tester `FuncDecl`s under the IR-lowered symbol
//! names so `encode_fn_call` resolves datatype operations to the native symbols.
//! The exhaustiveness/tester/selector/injectivity/disjointness facts are native
//! theory invariants (no hand-asserted axioms). `register_builtin_datatypes` is
//! called by setup to auto-register any `TrustVcType::Datatype` variables before
//! assumptions are encoded.

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, FuncDecl, Sort, Term};

use super::sanitize_symbol;
use super::types::sort_for_type;
use super::AYEncoder;
use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::{DatatypeVariant, TrustVcType};

#[path = "datatype_invariants.rs"]
mod invariants;

const DATATYPE_CONTEXT: &str = "register datatype";

#[derive(Debug, Clone)]
pub(crate) struct DatatypeEncoding {
    #[allow(dead_code)] // retained for diagnostics/debugging
    pub(crate) name: String,
    pub(crate) symbol_prefix: String,
    pub(crate) variants: Vec<VariantEncoding>,
}

impl DatatypeEncoding {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn variant(&self, name: &str) -> Option<&VariantEncoding> {
        self.variants.iter().find(|variant| variant.name == name)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct VariantEncoding {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) name: String,
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) constructor_name: String,
    pub(crate) constructor: ConstructorKind,
    pub(crate) fields: Vec<(String, crate::ir::TrustVcType)>,
    pub(crate) selectors: Vec<FuncDecl>,
    pub(crate) tester: FuncDecl,
}

#[derive(Debug, Clone)]
pub(crate) enum ConstructorKind {
    Constant(Term),
    Function(FuncDecl),
}

impl AYEncoder {
    /// Returns the cached datatype encoding for a registered datatype.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn datatype_encoding(&self, name: &str) -> Option<&DatatypeEncoding> {
        self.registries.datatypes.get(name)
    }

    /// Declares constructor/selector/tester symbols and asserts the soundness
    /// axioms for a builtin monomorphic datatype.
    ///
    /// Idempotent: re-registering the same datatype name reuses the cached
    /// encoding instead of re-declaring symbols.
    pub(crate) fn register_datatype(
        &mut self,
        name: &str,
        variants: &[DatatypeVariant],
    ) -> TrustVcResult<DatatypeEncoding> {
        if let Some(existing) = self.registries.datatypes.get(name) {
            return Ok(existing.clone());
        }
        if variants.is_empty() {
            return Err(datatype_error(format!(
                "Datatype '{name}' must declare at least one variant"
            )));
        }

        TrustVcType::Datatype {
            name: name.to_string(),
            variants: variants.to_vec(),
        }
        .validate_well_foundedness()
        .map_err(datatype_error)?;

        // Register the datatype natively with ay. This populates ay's native
        // constructor/selector/tester registry (`is_constructor` / `datatype_iter`),
        // which is the precondition for the mbqi tester-completion recognizers to
        // fire over symbolic datatype values — replacing the hand-rolled
        // exhaustiveness/tester/selector/injectivity/disjointness axioms with ay's
        // own sound native datatype theory.
        let dt_sort = datatype_sort_for(name, variants);
        self.solver
            .try_declare_datatype(&dt_sort)
            .map_err(|err| datatype_error(format!("Failed to declare datatype '{name}': {err}")))?;

        // The carrier sort for every datatype value is ay's native datatype sort,
        // which at the term level is `Sort::Uninterpreted(name)` (see
        // `Sort::as_term_sort`). Constructors/selectors/testers and datatype-typed
        // variables all share it.
        let carrier_sort = datatype_carrier_sort(name);
        let symbol_prefix = sanitize_symbol(name);
        let mut variant_encodings = Vec::with_capacity(variants.len());
        for variant in variants {
            variant_encodings.push(self.declare_variant_encoding(
                &symbol_prefix,
                name,
                variant,
                &carrier_sort,
                &dt_sort,
            )?);
        }

        let encoding = DatatypeEncoding {
            name: name.to_string(),
            symbol_prefix,
            variants: variant_encodings,
        };

        // Expose constructor symbols in the encoder's main lookup tables so
        // that `encode_fn_call` can resolve FnCall nodes produced by IR lowering
        // for datatype constructor expressions (e.g., `None`, `Some(42u64)`).
        // Also expose selectors/testers so field-access and datatype guard
        // expressions lowered to FnCall resolve through the same path.
        // Part of #2487, #2552.
        let datatype_ty = TrustVcType::Datatype {
            name: name.to_string(),
            variants: variants.to_vec(),
        };
        for ve in &encoding.variants {
            match &ve.constructor {
                ConstructorKind::Constant(term) => {
                    self.variables.insert(ve.constructor_name.clone(), *term);
                }
                ConstructorKind::Function(func) => {
                    self.fn_ctx
                        .functions
                        .insert(ve.constructor_name.clone(), func.clone());
                }
            }
            for (selector, (_, field_ty)) in ve.selectors.iter().zip(ve.fields.iter()) {
                let selector_name = selector.name().to_string();
                self.fn_ctx
                    .functions
                    .insert(selector_name.clone(), selector.clone());
                self.fn_ctx
                    .return_types
                    .insert(selector_name.clone(), field_ty.clone());
                self.fn_ctx
                    .param_types
                    .insert(selector_name.clone(), vec![datatype_ty.clone()]);
                self.state
                    .lowering_env
                    .insert_fn(selector_name.clone(), field_ty.clone());
                self.state
                    .lowering_env
                    .insert_fn_params(selector_name, vec![datatype_ty.clone()]);
            }
            let tester_name = ve.tester.name().to_string();
            self.fn_ctx
                .functions
                .insert(tester_name.clone(), ve.tester.clone());
            self.fn_ctx
                .return_types
                .insert(tester_name.clone(), TrustVcType::Bool);
            self.fn_ctx
                .param_types
                .insert(tester_name.clone(), vec![datatype_ty.clone()]);
            self.state
                .lowering_env
                .insert_fn(tester_name.clone(), TrustVcType::Bool);
            self.state
                .lowering_env
                .insert_fn_params(tester_name, vec![datatype_ty.clone()]);
        }

        // Soundness axioms (exhaustiveness / per-variant tester / selector
        // roundtrip / injectivity / variant + constructor-image disjointness) are
        // now native theory invariants established by `try_declare_datatype`, not
        // hand-asserted quantified UF axioms. The legacy `datatype_axioms.rs`
        // module is deleted; native registration is strictly more principled and
        // lets the mbqi recognizers discharge skipped quantifiers over symbolic
        // datatype values (a completeness gain, not a soundness change).
        self.assert_well_foundedness(name, &encoding, variants)?;
        self.registries
            .datatypes
            .insert(name.to_string(), encoding.clone());
        Ok(encoding)
    }

    /// Scans declared variable types for `TrustVcType::Datatype` entries and
    /// registers each distinct datatype with the solver. Called by
    /// `setup_from_prepared` after variable declarations, before assumptions.
    ///
    /// Idempotent via `register_datatype`'s cache check.
    /// Part of #1942 Slice 4.
    pub(crate) fn register_builtin_datatypes(&mut self) -> TrustVcResult<()> {
        let datatype_entries: Vec<(String, Vec<DatatypeVariant>)> = self
            .var_types
            .values()
            .filter_map(|ty| {
                if let crate::ir::TrustVcType::Datatype { name, variants } = ty {
                    Some((name.clone(), variants.clone()))
                } else {
                    None
                }
            })
            .collect();
        for (name, variants) in datatype_entries {
            self.register_datatype(&name, &variants)?;
        }
        Ok(())
    }

    /// Exposes `FuncDecl`/constant handles for one variant's
    /// constructor/selectors/tester. The datatype is already registered natively
    /// via `try_declare_datatype`; these `try_declare_fun` calls (over the native
    /// carrier sort) make the same symbols resolvable through the encoder's
    /// `FnCall` path (`try_apply`). They reuse the exact native symbol names —
    /// constructor `variant_symbol_name`, selector `selector_symbol_name`, tester
    /// `is-{constructor}` (`tester_symbol_name`) — so applied terms carry the
    /// symbols ay's recognizers and native theory key on. Re-declaring an
    /// already-registered symbol with the same signature is idempotent in ay's
    /// elaborator.
    fn declare_variant_encoding(
        &mut self,
        datatype_symbol: &str,
        datatype_name: &str,
        variant: &DatatypeVariant,
        carrier_sort: &Sort,
        dt_sort: &DatatypeSort,
    ) -> TrustVcResult<VariantEncoding> {
        let variant_symbol = format!("{}_{}", datatype_symbol, sanitize_symbol(&variant.name));
        let constructor_name = variant_symbol.clone();
        let constructor = if variant.fields.is_empty() {
            // Nullary constructor (e.g. `Opt_None`). Build its term through the
            // NATIVE datatype-constructor API so it carries real datatype
            // semantics — exhaustiveness/disjointness/injectivity. `declare_const`
            // is rejected by ay's fail-closed audit (re-declaring a name already
            // bound as a datatype constructor); an uninterpreted 0-ary function
            // (try_declare_fun + apply) parses but is NOT the native constructor,
            // so it drops disjointness — `E::B == E::A(..)` can then spuriously
            // hold, a false-verify (caught by concrete_trait_method_call_site's
            // enum_return liar). `try_datatype_constructor` returns the genuine
            // native nullary constructor term.
            let term = self
                .solver
                .try_datatype_constructor(dt_sort, &constructor_name, &[])
                .map_err(|err| {
                    datatype_error(format!(
                        "Failed to construct nullary constructor '{}' for '{}': {}",
                        constructor_name, variant.name, err
                    ))
                })?;
            ConstructorKind::Constant(term)
        } else {
            let domain: Vec<Sort> = variant
                .fields
                .iter()
                .map(|(_, ty)| field_sort_for(datatype_name, ty))
                .collect();
            let func = self
                .solver
                .try_declare_fun(&constructor_name, &domain, carrier_sort.clone())
                .map_err(|err| {
                    datatype_error(format!(
                        "Failed to declare constructor '{}' for '{}': {}",
                        constructor_name, variant.name, err
                    ))
                })?;
            ConstructorKind::Function(func)
        };

        let mut selectors = Vec::with_capacity(variant.fields.len());
        for (index, (field_name, field_ty)) in variant.fields.iter().enumerate() {
            let selector_name =
                format!("{}_{}", variant_symbol, selector_suffix(field_name, index));
            let selector = self
                .solver
                .try_declare_fun(
                    &selector_name,
                    std::slice::from_ref(carrier_sort),
                    field_sort_for(datatype_name, field_ty),
                )
                .map_err(|err| {
                    datatype_error(format!(
                        "Failed to declare selector '{}' for '{}::{}': {}",
                        selector_name, variant.name, field_name, err
                    ))
                })?;
            selectors.push(selector);
        }

        let tester_name = tester_symbol_name(datatype_name, &variant.name);
        let tester = self
            .solver
            .try_declare_fun(&tester_name, std::slice::from_ref(carrier_sort), Sort::Bool)
            .map_err(|err| {
                datatype_error(format!(
                    "Failed to declare tester '{}' for '{}': {}",
                    tester_name, variant.name, err
                ))
            })?;

        Ok(VariantEncoding {
            name: variant.name.clone(),
            constructor_name,
            constructor,
            fields: variant.fields.clone(),
            selectors,
            tester,
        })
    }

    fn fresh_field_vars(
        &mut self,
        datatype_symbol: &str,
        variant_name: &str,
        role: &str,
        variant: &DatatypeVariant,
    ) -> Vec<Term> {
        variant
            .fields
            .iter()
            .enumerate()
            .map(|(index, (_, field_ty))| {
                self.solver.fresh_var(
                    &format!(
                        "__{}_{}_{}_{}",
                        datatype_symbol,
                        sanitize_symbol(variant_name),
                        role,
                        index
                    ),
                    sort_for_type(field_ty),
                )
            })
            .collect()
    }

    fn apply_constructor(
        &mut self,
        constructor: &ConstructorKind,
        args: &[Term],
    ) -> TrustVcResult<Term> {
        match constructor {
            ConstructorKind::Constant(term) => {
                if !args.is_empty() {
                    return Err(datatype_error(format!(
                        "Nullary datatype constructor received {} argument(s)",
                        args.len()
                    )));
                }
                Ok(*term)
            }
            ConstructorKind::Function(func) => self.solver.try_apply(func, args).map_err(|err| {
                datatype_error(format!(
                    "Failed to apply datatype constructor '{}': {}",
                    func.name(),
                    err
                ))
            }),
        }
    }

    fn assert_axiom(&mut self, axiom: Term, detail: impl Into<String>) -> TrustVcResult<()> {
        self.solver
            .try_assert_term(axiom)
            .map_err(|err| datatype_error(format!("{}: {}", detail.into(), err)))
    }
}

fn datatype_error(detail: impl Into<String>) -> TrustVcError {
    TrustVcError::Encoding {
        context: DATATYPE_CONTEXT,
        detail: detail.into(),
    }
}

fn selector_suffix(field_name: &str, _index: usize) -> String {
    let suffix = sanitize_symbol(field_name);
    if suffix.is_empty() {
        // Legacy fallback: empty field names (e.g., positional tuple fields passed
        // as "") produce "Datatype" to preserve backward-compatible symbol names.
        "Datatype".to_string()
    } else {
        suffix
    }
}

/// Returns the backend carrier sort for datatype values of `datatype_name`.
///
/// ay registers a declared datatype's value sort as `Sort::Uninterpreted(name)`
/// internally (see `Sort::as_term_sort`), so every constructor/selector/tester
/// term and every datatype-typed variable shares this sort. `register_datatype`
/// passes the canonical (un-sanitized) datatype name to `try_declare_datatype`,
/// so the carrier name must match that string exactly.
pub(crate) fn datatype_carrier_sort(datatype_name: &str) -> Sort {
    Sort::Uninterpreted(datatype_name.to_string())
}

/// Resolves the backend sort of a constructor field, mapping a self-referential
/// `RecursiveRef` to the owning datatype's carrier sort (native datatypes carry a
/// real recursive sort rather than the legacy shared `Sort::Int`).
pub(crate) fn field_sort_for(datatype_name: &str, field_ty: &TrustVcType) -> Sort {
    match field_ty {
        TrustVcType::RecursiveRef(target) if target == datatype_name => {
            datatype_carrier_sort(datatype_name)
        }
        other => sort_for_type(other),
    }
}

/// Builds the ay-native `DatatypeSort` for a `TrustVcType::Datatype`.
///
/// Variants map to `DatatypeConstructor`s named with the existing
/// `variant_symbol_name` scheme (so IR-lowered constructor `FnCall`s resolve to
/// the same symbols); fields map to `DatatypeField`s named with
/// `selector_symbol_name` and sorts resolved via `field_sort_for` (recursively,
/// so nested datatype fields carry their own native carrier sort).
///
/// Pure builder: constructs the descriptor only. `register_datatype` passes the
/// result to `Solver::try_declare_datatype`, which populates ay's native
/// constructor/selector/tester registry (`is_constructor` / `datatype_iter`) —
/// the precondition for the mbqi tester-completion recognizers to fire.
pub(crate) fn datatype_sort_for(datatype_name: &str, variants: &[DatatypeVariant]) -> DatatypeSort {
    let constructors = variants
        .iter()
        .map(|variant| {
            let fields = variant
                .fields
                .iter()
                .enumerate()
                .map(|(index, (field_name, field_ty))| {
                    DatatypeField::new(
                        selector_symbol_name(datatype_name, &variant.name, field_name, index),
                        field_sort_for(datatype_name, field_ty),
                    )
                })
                .collect();
            DatatypeConstructor::new(variant_symbol_name(datatype_name, &variant.name), fields)
        })
        .collect();
    DatatypeSort::new(datatype_name.to_string(), constructors)
}

pub(crate) fn variant_symbol_name(datatype_name: &str, variant_name: &str) -> String {
    format!(
        "{}_{}",
        sanitize_symbol(datatype_name),
        sanitize_symbol(variant_name)
    )
}

/// Native datatype tester symbol: `is-{constructor}`.
///
/// ay's native datatype theory registers each variant's tester under this exact
/// `is-` (hyphen) name (`try_declare_datatype` → `is-{ctor}`), and the mbqi
/// tester-completion recognizers strip the `is-` prefix to recover the
/// constructor. The trust-vc tester symbol must match so IR-lowered tester
/// `FnCall`s build terms ay recognizes natively.
pub(crate) fn tester_symbol_name(datatype_name: &str, variant_name: &str) -> String {
    format!("is-{}", variant_symbol_name(datatype_name, variant_name))
}

pub(crate) fn selector_symbol_name(
    datatype_name: &str,
    variant_name: &str,
    field_name: &str,
    index: usize,
) -> String {
    format!(
        "{}_{}",
        variant_symbol_name(datatype_name, variant_name),
        selector_suffix(field_name, index)
    )
}
