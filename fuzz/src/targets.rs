// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::program::{ByteStream, FunctionSpec, GeneratedProgram};

const NUMERIC_TYPES: &[&str] = &["i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64"];
const SCALAR_TYPES: &[&str] = &["bool", "i32", "u32", "i64", "u64"];

pub fn ensures_false_program(data: &[u8]) -> GeneratedProgram {
    let mut bytes = ByteStream::new(data);
    let params = parameter_list(&mut bytes, SCALAR_TYPES, 3);
    let mut requires = Vec::new();

    if let Some(first_param) = params.first().map(|param| param_name(param)) {
        requires.push(format!("{first_param} == {first_param}"));
    }
    if bytes.flag() {
        requires.push("true".to_string());
    }

    FunctionSpec {
        params,
        requires,
        ensures: vec!["false".to_string()],
        return_ty: "i32",
        body: "0",
    }
    .render("ensures_false", "random ensures(false) program")
}

pub fn strict_inequality_program(data: &[u8]) -> GeneratedProgram {
    let mut bytes = ByteStream::new(data);
    let x_ty = *bytes.choose(NUMERIC_TYPES);
    let mut params = vec![format!("x: {x_ty}")];

    if bytes.flag() {
        params.push(format!("y: {}", bytes.choose(NUMERIC_TYPES)));
    }

    let mut requires = vec!["x == x".to_string()];
    if bytes.flag() {
        requires.push("true".to_string());
    }

    FunctionSpec {
        params,
        requires,
        ensures: vec!["x > x".to_string()],
        return_ty: "i32",
        body: "0",
    }
    .render("strict_inequality", "random ensures(x > x) program")
}

pub fn mode_crossing_program(data: &[u8]) -> GeneratedProgram {
    let mut bytes = ByteStream::new(data);

    match bytes.choose_index(4) {
        0 => seq_signed_quantifier_false(&mut bytes),
        1 => map_get_cross_width_false(&mut bytes),
        2 => seq_contains_cross_width_false(&mut bytes),
        _ => seq_unsigned_quantifier_false(&mut bytes),
    }
}

pub fn collections_contradiction_program(data: &[u8]) -> GeneratedProgram {
    let mut bytes = ByteStream::new(data);

    match bytes.choose_index(7) {
        0 => seq_push_wrong_length(&mut bytes),
        1 => seq_concat_wrong_length(&mut bytes),
        2 => set_insert_wrong_lookup(&mut bytes),
        3 => set_union_wrong_membership(&mut bytes),
        4 => set_intersect_wrong_membership(&mut bytes),
        5 => seq_take_wrong_total_length(&mut bytes),
        _ => seq_subrange_wrong_total_length(&mut bytes),
    }
}

fn parameter_list(bytes: &mut ByteStream<'_>, types: &[&str], max_params: usize) -> Vec<String> {
    let names = ["x", "y", "z"];
    let count = bytes.choose_index(max_params + 1);
    names
        .into_iter()
        .take(count)
        .map(|name| format!("{name}: {}", bytes.choose(types)))
        .collect()
}

fn param_name(param: &str) -> &str {
    param.split(':').next().unwrap_or(param).trim()
}

fn seq_signed_quantifier_false(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let len = bytes.small_u64(3) + 1;
    let bad_index = bytes.choose_index(len as usize);
    let negative = bytes.small_i32(-32, -1);

    FunctionSpec {
        params: vec!["s: Seq<i32>".to_string()],
        requires: vec![
            format!("s.len() == {len}"),
            format!("s.index({bad_index}) == {negative}"),
        ],
        ensures: vec![format!("forall(|i: u64| !(i < {len}) || s.index(i) >= 0)")],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "mode_crossing",
        "signed Seq quantifier with negative element and Int-mode comparison",
    )
}

fn map_get_cross_width_false(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let key = bytes.small_i32(0, 15);
    let value = bytes.small_u64(200) + 1;

    FunctionSpec {
        params: vec!["m: Map<i32, i64>".to_string(), "x: u32".to_string()],
        requires: vec![format!("m.get({key}) == {value}"), format!("x == {value}")],
        ensures: vec![format!("m.get({key}) != x")],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "mode_crossing",
        "Map::get cross-width equality forced false through contradictory postcondition",
    )
}

fn seq_contains_cross_width_false(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let value = bytes.small_u64(200) + 1;

    FunctionSpec {
        params: vec!["s: Seq<i64>".to_string(), "x: i32".to_string()],
        requires: vec![
            "s.len() == 1".to_string(),
            format!("s.index(0) == {value}"),
            format!("x == {value}"),
        ],
        ensures: vec!["!s.contains(x)".to_string()],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "mode_crossing",
        "Seq::contains cross-width coercion with contradictory negated membership",
    )
}

fn seq_unsigned_quantifier_false(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let len = bytes.small_u64(3) + 1;
    let bad_index = bytes.choose_index(len as usize);
    let value = bytes.small_u64(16);

    FunctionSpec {
        params: vec!["s: Seq<u32>".to_string()],
        requires: vec![
            format!("s.len() == {len}"),
            format!("s.index({bad_index}) == {value}"),
        ],
        ensures: vec![format!("forall(|i: u64| !(i < {len}) || s.index(i) < 0)")],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "mode_crossing",
        "unsigned Seq quantifier crossing into Int-mode with impossible negativity claim",
    )
}

fn seq_push_wrong_length(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let len = bytes.small_u64(6);

    FunctionSpec {
        params: vec!["s: Seq<i32>".to_string(), "v: i32".to_string()],
        requires: vec![format!("s.len() == {len}")],
        ensures: vec![format!("s.push(v).len() == {len}")],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "collections_contradiction",
        "Seq::push length preserved instead of incremented",
    )
}

fn seq_concat_wrong_length(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let left = bytes.small_u64(4);
    let right = bytes.small_u64(3) + 1;
    let wrong_total = left + right - 1;

    FunctionSpec {
        params: vec!["a: Seq<i32>".to_string(), "b: Seq<i32>".to_string()],
        requires: vec![format!("a.len() == {left}"), format!("b.len() == {right}")],
        ensures: vec![format!("a.concat(b).len() == {wrong_total}")],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "collections_contradiction",
        "Seq::concat wrong total length",
    )
}

fn set_insert_wrong_lookup(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let inserted = bytes.small_i32(0, 31);
    let missing = inserted + 1;

    FunctionSpec {
        params: vec!["s: Set<i32>".to_string()],
        requires: Vec::new(),
        ensures: vec![format!("s.insert({inserted}).contains({missing})")],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "collections_contradiction",
        "Set::insert followed by lookup of a different key",
    )
}

fn set_union_wrong_membership(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let value = bytes.small_i32(0, 31);

    FunctionSpec {
        params: vec!["a: Set<i32>".to_string(), "b: Set<i32>".to_string()],
        requires: vec![
            format!("!a.contains({value})"),
            format!("!b.contains({value})"),
        ],
        ensures: vec![format!("a.union(b).contains({value})")],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "collections_contradiction",
        "Set::union contains a value excluded from both inputs",
    )
}

fn set_intersect_wrong_membership(bytes: &mut ByteStream<'_>) -> GeneratedProgram {
    let value = bytes.small_i32(0, 31);

    FunctionSpec {
        params: vec!["a: Set<i32>".to_string(), "b: Set<i32>".to_string()],
        requires: vec![
            format!("a.contains({value})"),
            format!("!b.contains({value})"),
        ],
        ensures: vec![format!("a.intersect(b).contains({value})")],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "collections_contradiction",
        "Set::intersect contains a value missing from one input",
    )
}

fn seq_take_wrong_total_length(_: &mut ByteStream<'_>) -> GeneratedProgram {
    FunctionSpec {
        params: vec!["s: Seq<i32>".to_string()],
        requires: vec!["s.len() == 5".to_string()],
        ensures: vec!["s.take(3).len() + s.len() == 7".to_string()],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "collections_contradiction",
        "Seq::take corrupts source metadata in the postcondition",
    )
}

fn seq_subrange_wrong_total_length(_: &mut ByteStream<'_>) -> GeneratedProgram {
    FunctionSpec {
        params: vec!["s: Seq<i32>".to_string()],
        requires: vec!["s.len() == 5".to_string()],
        ensures: vec!["s.subrange(0, 3).len() + s.len() == 7".to_string()],
        return_ty: "i32",
        body: "0",
    }
    .render(
        "collections_contradiction",
        "Seq::subrange corrupts source metadata in the postcondition",
    )
}
