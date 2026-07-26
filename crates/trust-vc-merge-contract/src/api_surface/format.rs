// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustdoc_types::{
    Abi, AssocItemConstraint, AssocItemConstraintKind, Function, FunctionHeader, FunctionPointer,
    FunctionSignature, GenericArg, GenericArgs, GenericBound, GenericParamDef, GenericParamDefKind,
    Term, Type,
};

pub(super) fn format_function_line(path: &str, function: &Function) -> String {
    let prefix = format_function_prefix(&function.header);
    let generics = format_generics(&function.generics);
    let signature = format_function_signature(&function.sig);
    format!("{prefix}fn {path}{generics}{signature}")
}

pub(super) fn format_generics(generics: &rustdoc_types::Generics) -> String {
    let params = generics
        .params
        .iter()
        .map(format_generic_param)
        .collect::<Vec<_>>();
    if params.is_empty() {
        String::new()
    } else {
        format!("<{}>", params.join(", "))
    }
}

pub(super) fn format_type(type_: &Type) -> String {
    match type_ {
        Type::ResolvedPath(path) => format_path(path),
        Type::DynTrait(dyn_trait) => {
            let mut parts = dyn_trait
                .traits
                .iter()
                .map(|poly_trait| format_path(&poly_trait.trait_))
                .collect::<Vec<_>>();
            if let Some(lifetime) = &dyn_trait.lifetime {
                parts.push(lifetime.clone());
            }
            format!("dyn {}", parts.join(" + "))
        }
        Type::Generic(name) => name.clone(),
        Type::Primitive(name) => name.clone(),
        Type::FunctionPointer(pointer) => format_function_pointer(pointer),
        Type::Tuple(types) => match types.as_slice() {
            [] => "()".to_owned(),
            [only] => format!("({},)", format_type(only)),
            _ => format!(
                "({})",
                types.iter().map(format_type).collect::<Vec<_>>().join(", ")
            ),
        },
        Type::Slice(type_) => format!("[{}]", format_type(type_)),
        Type::Array { type_, len } => format!("[{}; {len}]", format_type(type_)),
        Type::Pat { type_, .. } => format!("{} is _", format_type(type_)),
        Type::ImplTrait(bounds) => format!(
            "impl {}",
            bounds
                .iter()
                .map(format_generic_bound)
                .collect::<Vec<_>>()
                .join(" + ")
        ),
        Type::Infer => "_".to_owned(),
        Type::RawPointer { is_mutable, type_ } => {
            let qualifier = if *is_mutable { "mut" } else { "const" };
            format!("*{qualifier} {}", format_type(type_))
        }
        Type::BorrowedRef {
            lifetime,
            is_mutable,
            type_,
        } => {
            let lifetime = lifetime
                .as_ref()
                .map(|lifetime| format!("{lifetime} "))
                .unwrap_or_default();
            let qualifier = if *is_mutable { "mut " } else { "" };
            format!("&{lifetime}{qualifier}{}", format_type(type_))
        }
        Type::QualifiedPath {
            name,
            args,
            self_type,
            trait_,
        } => {
            let args = args.as_deref().map(format_generic_args).unwrap_or_default();
            match trait_ {
                Some(trait_) if !trait_.path.is_empty() => format!(
                    "<{} as {}>::{}{args}",
                    format_type(self_type),
                    format_path(trait_),
                    name
                ),
                _ => format!("{}::{}{args}", format_type(self_type), name),
            }
        }
    }
}

fn format_function_prefix(header: &FunctionHeader) -> String {
    let mut parts = Vec::new();
    if header.is_const {
        parts.push("const".to_owned());
    }
    if header.is_async {
        parts.push("async".to_owned());
    }
    if header.is_unsafe {
        parts.push("unsafe".to_owned());
    }
    if !matches!(header.abi, Abi::Rust) {
        parts.push(format!("extern {}", format_abi(&header.abi)));
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!("{} ", parts.join(" "))
    }
}

fn format_abi(abi: &Abi) -> String {
    match abi {
        Abi::Rust => "\"Rust\"".to_owned(),
        Abi::C { unwind } => format_abi_name("C", *unwind),
        Abi::Cdecl { unwind } => format_abi_name("cdecl", *unwind),
        Abi::Stdcall { unwind } => format_abi_name("stdcall", *unwind),
        Abi::Fastcall { unwind } => format_abi_name("fastcall", *unwind),
        Abi::Aapcs { unwind } => format_abi_name("aapcs", *unwind),
        Abi::Win64 { unwind } => format_abi_name("win64", *unwind),
        Abi::SysV64 { unwind } => format_abi_name("sysv64", *unwind),
        Abi::System { unwind } => format_abi_name("system", *unwind),
        Abi::Other(name) => format!("\"{name}\""),
    }
}

fn format_abi_name(name: &str, unwind: bool) -> String {
    if unwind {
        format!("\"{name}-unwind\"")
    } else {
        format!("\"{name}\"")
    }
}

fn format_function_signature(signature: &FunctionSignature) -> String {
    let mut inputs = signature
        .inputs
        .iter()
        .map(|(name, type_)| format!("{name}: {}", format_type(type_)))
        .collect::<Vec<_>>();
    if signature.is_c_variadic {
        inputs.push("...".to_owned());
    }
    let output = signature
        .output
        .as_ref()
        .map(|type_| format!(" -> {}", format_type(type_)))
        .unwrap_or_default();
    format!("({}){output}", inputs.join(", "))
}

fn format_generic_param(param: &GenericParamDef) -> String {
    match &param.kind {
        GenericParamDefKind::Lifetime { .. } => param.name.clone(),
        GenericParamDefKind::Type { .. } => param.name.clone(),
        GenericParamDefKind::Const { type_, .. } => {
            format!("const {}: {}", param.name, format_type(type_))
        }
    }
}

fn format_function_pointer(pointer: &FunctionPointer) -> String {
    let prefix = format_function_prefix(&pointer.header);
    let generics = if pointer.generic_params.is_empty() {
        String::new()
    } else {
        format!(
            "for<{}> ",
            pointer
                .generic_params
                .iter()
                .map(format_generic_param)
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!(
        "{generics}{prefix}fn{}",
        format_function_signature(&pointer.sig)
    )
}

fn format_path(path: &rustdoc_types::Path) -> String {
    let args = path
        .args
        .as_deref()
        .map(format_generic_args)
        .unwrap_or_default();
    format!("{}{}", path.path, args)
}

fn format_generic_args(args: &GenericArgs) -> String {
    match args {
        GenericArgs::AngleBracketed { args, constraints } => {
            let mut parts = args.iter().map(format_generic_arg).collect::<Vec<_>>();
            parts.extend(constraints.iter().map(format_assoc_item_constraint));
            format!("<{}>", parts.join(", "))
        }
        GenericArgs::Parenthesized { inputs, output } => {
            let output = output
                .as_ref()
                .map(|type_| format!(" -> {}", format_type(type_)))
                .unwrap_or_default();
            format!(
                "({}){}",
                inputs
                    .iter()
                    .map(format_type)
                    .collect::<Vec<_>>()
                    .join(", "),
                output
            )
        }
        GenericArgs::ReturnTypeNotation => "(..)".to_owned(),
    }
}

fn format_generic_arg(arg: &GenericArg) -> String {
    match arg {
        GenericArg::Lifetime(lifetime) => lifetime.clone(),
        GenericArg::Type(type_) => format_type(type_),
        GenericArg::Const(constant) => constant
            .value
            .clone()
            .unwrap_or_else(|| constant.expr.clone()),
        GenericArg::Infer => "_".to_owned(),
    }
}

fn format_assoc_item_constraint(constraint: &AssocItemConstraint) -> String {
    let args = constraint
        .args
        .as_deref()
        .map(format_generic_args)
        .unwrap_or_default();
    let binding = match &constraint.binding {
        AssocItemConstraintKind::Equality(term) => format!(" = {}", format_term(term)),
        AssocItemConstraintKind::Constraint(bounds) => format!(
            ": {}",
            bounds
                .iter()
                .map(format_generic_bound)
                .collect::<Vec<_>>()
                .join(" + ")
        ),
    };
    format!("{}{}{}", constraint.name, args, binding)
}

fn format_generic_bound(bound: &GenericBound) -> String {
    match bound {
        GenericBound::TraitBound {
            trait_, modifier, ..
        } => {
            let modifier = match modifier {
                rustdoc_types::TraitBoundModifier::None => "",
                rustdoc_types::TraitBoundModifier::Maybe => "?",
                rustdoc_types::TraitBoundModifier::MaybeConst => "~const ",
            };
            format!("{modifier}{}", format_path(trait_))
        }
        GenericBound::Outlives(lifetime) => lifetime.clone(),
        GenericBound::Use(args) => format!(
            "use<{}>",
            args.iter()
                .map(|arg| match arg {
                    rustdoc_types::PreciseCapturingArg::Lifetime(lifetime) => lifetime.clone(),
                    rustdoc_types::PreciseCapturingArg::Param(param) => param.clone(),
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn format_term(term: &Term) -> String {
    match term {
        Term::Type(type_) => format_type(type_),
        Term::Constant(constant) => constant
            .value
            .clone()
            .unwrap_or_else(|| constant.expr.clone()),
    }
}
