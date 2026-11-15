// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Concrete replay of solver witnesses through trust-ir's own reference
//! interpreter (`trust_ir::Interpreter`).
//!
//! The interpreter is written independently of this lane's lowering, so it
//! is the semantic check on every witness the solver hands back: a refutation
//! is reported only if the witness really fails the site, and a discharge
//! only if some input really reaches it. A witness that does not replay is
//! downgraded to `Unknown`, never reported.
//!
//! Each variant is the target function alone, re-typed to return nothing,
//! truncated right after the site with `Return []`, and some `Assert`s
//! neutralized into `Copy Bool` of their condition.
//!
//! # The variant is NOT always the module as written
//!
//! A `Undef Tuple` seed is also replaced by an all-zero constant, because the
//! pinned interpreter refuses to execute an `Undef` at a tuple type
//! (`interpret.rs:1194` -> `scalar_poison`: aggregate poison is unmodelled). Which particular constant is chosen is unobservable —
//! the checker refuses every read of a field no `InsertField` wrote, and an
//! aggregate cannot be used where a scalar is required — so the zero seeding
//! instantiates the havoc arbitrarily and nothing can tell. But the variant is
//! then a DIFFERENT body from the one the obligation is about, and every
//! verdict built on it is tagged
//! [`super::BodyReading::HavocInstantiatedUndef`] all the way out to the
//! caller, witness included. See the module doc of `super`.

use std::collections::BTreeSet;

use trust_ir::{
    BlockId, Constant, FuncTy, FuncTyId, Function, Inst, InstrNode, InterpretErrorCode,
    InterpretOptions, InterpretValue, Interpreter, Module, Ty, ValueId,
};
use trust_vc_core::CounterexampleBinding;

use super::check::{CheckedBody, ScalarTy};
use super::lower::value_var_name;
use super::{BodyReading, TrustIrBodyWitness, TrustIrScalar};

/// Which `Assert`s a variant keeps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Variant {
    /// Only the site's `Assert` is kept.
    Site,
    /// No `Assert` is kept: reaching the end means every premise held.
    Pre,
    /// Every `Assert` before the site is kept; the site's is neutralized.
    Prior,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Outcome {
    Reached,
    Panic,
    UndefinedBehavior,
    /// A false `Assume` (trust-ir `InterpretErrorCode::AssumeViolated`,
    /// WS2.11): the input lies outside the assumed domain. Named apart from
    /// program UB upstream; decisive for nothing here, like UB.
    AssumeViolated,
    Other(String),
}

const REPLAY_FUEL: u64 = 1_000_000;

fn zero_constant(ty: &Ty) -> Constant {
    if matches!(ty, Ty::Bool) {
        Constant::Bool(false)
    } else {
        Constant::Int(0)
    }
}

/// Build the executable variant for the site `(block, inst_index)`.
pub(crate) fn build_variant(
    module: &Module,
    function: &Function,
    body: &CheckedBody,
    site: (BlockId, u32),
    variant: Variant,
) -> Result<Module, String> {
    let mut variant_module = module.clone();
    variant_module
        .functions
        .retain(|candidate| candidate.id == function.id);
    let sig = variant_module
        .func_type(function.ty)
        .cloned()
        .ok_or_else(|| format!("function type functy.{} is missing", function.ty.0))?;
    let new_ty = FuncTyId::new(
        u32::try_from(variant_module.func_types.len())
            .map_err(|_| "function type table exceeds u32".to_string())?,
    );
    variant_module.func_types.push(FuncTy {
        params: sig.params,
        returns: Vec::new(),
        is_vararg: false,
        abi: None,
    });
    let site_chain_index = body
        .chain
        .iter()
        .position(|block| *block == site.0)
        .ok_or_else(|| format!("site block bb{} is not on the chain", site.0 .0))?;
    let keep = body.chain[..=site_chain_index]
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();

    let [target] = variant_module.functions.as_mut_slice() else {
        return Err("target function is missing or duplicated".to_string());
    };
    target.ty = new_ty;
    target.blocks.retain(|block| keep.contains(&block.id));
    let mut next_value = target.max_value_id().saturating_add(1);
    for block in &mut target.blocks {
        let is_site_block = block.id == site.0;
        if is_site_block {
            block.body.truncate(site.1 as usize + 1);
            block
                .body
                .push(InstrNode::new(Inst::Return { values: Vec::new() }));
        }
        for (index, node) in block.body.iter_mut().enumerate() {
            let is_site = is_site_block && index == site.1 as usize;
            match &node.inst {
                Inst::Undef {
                    ty: Ty::Tuple(fields),
                } => {
                    let zeros = fields.iter().map(zero_constant).collect();
                    node.inst = Inst::Const {
                        ty: Ty::Tuple(fields.clone()),
                        value: Constant::Aggregate(zeros),
                    };
                }
                Inst::Assert { cond, .. } => {
                    let neutralize = match variant {
                        Variant::Site => !is_site,
                        Variant::Pre => true,
                        Variant::Prior => is_site,
                    };
                    if neutralize {
                        node.inst = Inst::Copy {
                            ty: Ty::Bool,
                            operand: *cond,
                        };
                        node.results = vec![ValueId::new(next_value)];
                        next_value = next_value.saturating_add(1);
                    }
                }
                _ => {}
            }
        }
    }
    Ok(variant_module)
}

pub(crate) fn witness_args(witness: &TrustIrBodyWitness) -> Result<Vec<InterpretValue>, String> {
    witness
        .params
        .iter()
        .map(|(_, scalar)| match scalar {
            TrustIrScalar::Bool(b) => Ok(InterpretValue::bool(*b)),
            TrustIrScalar::Int { ty, value } => {
                InterpretValue::int(ty.clone(), *value).map_err(|error| error.to_string())
            }
        })
        .collect()
}

/// Execute an already-built variant on `witness`.
pub(crate) fn execute(
    module: &Module,
    function: &Function,
    witness: &TrustIrBodyWitness,
) -> Outcome {
    let args = match witness_args(witness) {
        Ok(args) => args,
        Err(error) => return Outcome::Other(format!("witness is not executable: {error}")),
    };
    let options = InterpretOptions {
        fuel: REPLAY_FUEL,
        ..InterpretOptions::default()
    };
    match Interpreter::with_module(module)
        .with_options(options)
        .execute_func(function.id, args)
    {
        Ok(_) => Outcome::Reached,
        Err(error) => match error.code {
            InterpretErrorCode::Panic => Outcome::Panic,
            InterpretErrorCode::UndefinedBehavior => Outcome::UndefinedBehavior,
            InterpretErrorCode::AssumeViolated => Outcome::AssumeViolated,
            // Every other code is a refusal of the interpreter to run the
            // variant; `Other` is decisive for nothing (the caller downgrades
            // to Unknown), so a code trust-ir adds later fails closed here.
            _ => Outcome::Other(error.to_string()),
        },
    }
}

/// Build and execute one variant.
pub(crate) fn replay(
    module: &Module,
    function: &Function,
    body: &CheckedBody,
    site: (BlockId, u32),
    variant: Variant,
    witness: &TrustIrBodyWitness,
) -> Outcome {
    match build_variant(module, function, body, site, variant) {
        Ok(variant_module) => execute(&variant_module, function, witness),
        Err(error) => Outcome::Other(format!("replay variant not buildable: {error}")),
    }
}

fn parse_int(text: &str, bits: u32, signed: bool) -> Result<i128, String> {
    let (min, max) = ScalarTy::Int { bits, signed }
        .int_bounds()
        .ok_or_else(|| "not an integer type".to_string())?;
    let radix_raw = text
        .strip_prefix("#x")
        .map(|digits| u128::from_str_radix(digits, 16))
        .or_else(|| {
            text.strip_prefix("#b")
                .map(|digits| u128::from_str_radix(digits, 2))
        });
    let value = match radix_raw {
        Some(raw) => {
            let raw = raw.map_err(|error| format!("unreadable bit-vector `{text}`: {error}"))?;
            if bits < 128 && raw >> bits != 0 {
                return Err(format!("bit-vector `{text}` is wider than {bits} bits"));
            }
            let raw = i128::try_from(raw).map_err(|_| format!("`{text}` exceeds i128"))?;
            if signed && raw > max {
                raw - (1i128 << bits)
            } else {
                raw
            }
        }
        None => text
            .parse::<i128>()
            .map_err(|error| format!("unreadable integer `{text}`: {error}"))?,
    };
    if value < min || value > max {
        return Err(format!("model value {value} is outside [{min}, {max}]"));
    }
    Ok(value)
}

/// Read the entry parameters out of the solver's counterexample bindings.
/// A parameter the model does not mention is unconstrained and replays as 0
/// (or `false`); a value that cannot be read or is out of range is an error.
pub(crate) fn witness_from_bindings(
    body: &CheckedBody,
    bindings: &[CounterexampleBinding],
    reading: BodyReading,
) -> Result<TrustIrBodyWitness, String> {
    let mut params = Vec::with_capacity(body.params.len());
    for (value, ty) in &body.params {
        let name = value_var_name(*value);
        let mut matching = bindings.iter().filter(|binding| binding.raw_name == name);
        let first = matching.next();
        if let (Some(first), Some(second)) = (first, matching.next()) {
            if first.value != second.value {
                return Err(format!("model binds {name} twice with different values"));
            }
        }
        let scalar = match (ty, first) {
            (ScalarTy::Bool, None) => TrustIrScalar::Bool(false),
            (ScalarTy::Bool, Some(binding)) => match binding.value.trim() {
                "true" => TrustIrScalar::Bool(true),
                "false" => TrustIrScalar::Bool(false),
                other => return Err(format!("unreadable Bool `{other}` for {name}")),
            },
            (ScalarTy::Int { .. }, None) => TrustIrScalar::Int {
                ty: ty.to_ty(),
                value: 0,
            },
            (ScalarTy::Int { bits, signed }, Some(binding)) => TrustIrScalar::Int {
                ty: ty.to_ty(),
                value: parse_int(binding.value.trim(), *bits, *signed)
                    .map_err(|error| format!("{name}: {error}"))?,
            },
        };
        params.push((*value, scalar));
    }
    Ok(TrustIrBodyWitness { params, reading })
}

#[cfg(test)]
mod tests {
    use super::parse_int;

    #[test]
    fn model_values_parse_by_width_and_signedness() {
        assert_eq!(parse_int("-128", 8, true), Ok(-128));
        assert_eq!(parse_int("255", 8, false), Ok(255));
        assert!(parse_int("256", 8, false).is_err());
        assert!(parse_int("128", 8, true).is_err());
        assert_eq!(parse_int("#xff", 8, true), Ok(-1));
        assert_eq!(parse_int("#xff", 8, false), Ok(255));
        assert_eq!(parse_int("#b10000000", 8, true), Ok(-128));
        assert!(parse_int("#x1ff", 8, false).is_err());
        assert!(parse_int("abc", 8, false).is_err());
    }
}
