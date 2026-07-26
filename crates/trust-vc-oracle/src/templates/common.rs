// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::backend::ProposedAnnotations;
use crate::engine::FunctionSignature;
use crate::feedback::{CounterexampleField, ProofFeedback};

const UNSIGNED_TYPES: &[&str] = &["u8", "u16", "u32", "u64", "u128", "usize"];
const SIGNED_TYPES: &[&str] = &["i8", "i16", "i32", "i64", "i128", "isize"];
const COLLECTION_PREFIXES: &[&str] = &["Vec<", "Seq<", "&[", "Array<", "List<"];

pub(crate) fn normalize_type(ty: &str) -> String {
    ty.chars().filter(|ch| !ch.is_whitespace()).collect()
}

pub(crate) fn same_type(left: &str, right: &str) -> bool {
    normalize_type(left) == normalize_type(right)
}

pub(crate) fn is_numeric(ty: &str) -> bool {
    let ty = normalize_type(ty);
    UNSIGNED_TYPES.contains(&ty.as_str()) || SIGNED_TYPES.contains(&ty.as_str())
}

pub(crate) fn is_unsigned(ty: &str) -> bool {
    let ty = normalize_type(ty);
    UNSIGNED_TYPES.contains(&ty.as_str())
}

pub(crate) fn is_collection(ty: &str) -> bool {
    let ty = normalize_type(ty);
    COLLECTION_PREFIXES
        .iter()
        .any(|prefix| ty.starts_with(prefix))
}

pub(crate) fn is_bool(ty: &str) -> bool {
    normalize_type(ty) == "bool"
}

pub(crate) fn is_option(ty: &str) -> bool {
    normalize_type(ty).starts_with("Option<")
}

pub(crate) fn is_result(ty: &str) -> bool {
    normalize_type(ty).starts_with("Result<")
}

pub(crate) fn returns_numeric(sig: &FunctionSignature) -> bool {
    sig.return_type.as_deref().is_some_and(is_numeric)
}

pub(crate) fn returns_collection(sig: &FunctionSignature) -> bool {
    sig.return_type.as_deref().is_some_and(is_collection)
}

pub(crate) fn returns_bool(sig: &FunctionSignature) -> bool {
    sig.return_type.as_deref().is_some_and(is_bool)
}

pub(crate) fn returns_option(sig: &FunctionSignature) -> bool {
    sig.return_type.as_deref().is_some_and(is_option)
}

pub(crate) fn returns_result(sig: &FunctionSignature) -> bool {
    sig.return_type.as_deref().is_some_and(is_result)
}

pub(crate) fn has_single_numeric_param(sig: &FunctionSignature) -> bool {
    sig.params.len() == 1 && is_numeric(&sig.params[0].1)
}

pub(crate) fn has_single_collection_param(sig: &FunctionSignature) -> bool {
    sig.params.len() == 1 && is_collection(&sig.params[0].1)
}

pub(crate) fn has_two_same_type_numeric_params(sig: &FunctionSignature) -> bool {
    sig.params.len() == 2
        && is_numeric(&sig.params[0].1)
        && same_type(&sig.params[0].1, &sig.params[1].1)
}

pub(crate) fn has_two_same_type_params(sig: &FunctionSignature) -> bool {
    sig.params.len() == 2 && same_type(&sig.params[0].1, &sig.params[1].1)
}

pub(crate) fn has_single_param_matching_return(sig: &FunctionSignature) -> bool {
    sig.params.len() == 1
        && sig
            .return_type
            .as_deref()
            .is_some_and(|ret| same_type(ret, &sig.params[0].1))
}

pub(crate) fn has_param_named(sig: &FunctionSignature, candidates: &[&str]) -> bool {
    sig.params
        .iter()
        .any(|(name, _)| candidates.contains(&name.as_str()))
}

pub(crate) fn numeric_params<'a>(
    sig: &'a FunctionSignature,
) -> impl Iterator<Item = &'a (String, String)> + 'a {
    sig.params.iter().filter(|(_, ty)| is_numeric(ty))
}

pub(crate) fn proposal(requires: Vec<String>, ensures: Vec<String>) -> ProposedAnnotations {
    ProposedAnnotations {
        requires,
        ensures,
        invariants: vec![],
        decreases: vec![],
        raw_response: String::new(),
    }
}

pub(crate) fn proposal_from_strs(requires: &[&str], ensures: &[&str]) -> ProposedAnnotations {
    proposal(
        requires
            .iter()
            .map(|clause| (*clause).to_string())
            .collect(),
        ensures.iter().map(|clause| (*clause).to_string()).collect(),
    )
}

pub(crate) fn counterexample_field<'a>(
    feedback: &'a ProofFeedback,
    name: &str,
) -> Option<&'a CounterexampleField> {
    match feedback {
        ProofFeedback::Failed {
            counterexamples, ..
        } => counterexamples.iter().find(|field| field.name == name),
        _ => None,
    }
}

pub(crate) fn counterexample_value<'a>(feedback: &'a ProofFeedback, name: &str) -> Option<&'a str> {
    counterexample_field(feedback, name).map(|field| field.value.as_str())
}

pub(crate) fn counterexample_i64(feedback: &ProofFeedback, name: &str) -> Option<i64> {
    counterexample_value(feedback, name).and_then(|value| value.parse().ok())
}
