// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Display exact function definitions from the solver's published model.
//! These bindings are diagnostics and confer no verification authority.

use super::*;
use ay_frontend::sexp::parse_sexps;

const MAX_MODEL_BYTES: usize = 512 * 1024;
const MAX_MODEL_NODES: usize = 32_768;
const MAX_MODEL_DEPTH: usize = 64;

pub(in crate::encoder) fn published_function_bindings(
    model: &str,
    metadata: &HashMap<String, CounterexampleVarMeta>,
) -> Result<Vec<CounterexampleBinding>, &'static str> {
    if model.len() > MAX_MODEL_BYTES {
        return Err("function model exceeds display size limit");
    }
    let expressions = parse_sexps(model).map_err(|_| "malformed published function model")?;
    if expressions.len() > MAX_MODEL_NODES {
        return Err("function model exceeds display traversal limit");
    }
    let mut pending: Vec<_> = expressions
        .iter()
        .map(|expression| (expression, 0usize))
        .collect();
    let mut visited = 0usize;
    while let Some((expression, depth)) = pending.pop() {
        visited += 1;
        if visited > MAX_MODEL_NODES || depth > MAX_MODEL_DEPTH {
            return Err("function model exceeds display traversal limit");
        }
        if let Some(children) = expression.as_list() {
            if pending.len().saturating_add(children.len()) > MAX_MODEL_NODES {
                return Err("function model exceeds display traversal limit");
            }
            pending.extend(children.iter().map(|child| (child, depth + 1)));
        }
    }
    let [root] = expressions.as_slice() else {
        return Err("published model is not one model document");
    };
    let entries = root.as_list().ok_or("published model is not a list")?;
    let definitions = if entries.first().is_some_and(|tag| tag.is_symbol("model")) {
        &entries[1..]
    } else {
        entries
    };
    let mut bindings = Vec::new();
    let mut names = std::collections::HashSet::new();
    for definition in definitions {
        let Some([tag, name, parameters, result, body]) = definition.as_list() else {
            return Err("malformed published function definition");
        };
        if !tag.is_symbol("define-fun") {
            return Err("unsupported published model entry");
        }
        let name = name.as_symbol().ok_or("invalid published function name")?;
        if !names.insert(name) {
            return Err("duplicate published model name");
        }
        let parameters = parameters.as_list().ok_or("invalid function parameters")?;
        if parameters.is_empty() {
            continue; // Scalar assignments already have typed source rendering.
        }
        let meta = metadata
            .get(name)
            .cloned()
            .unwrap_or_else(|| counterexample_names::default_meta(name));
        if !meta.visible {
            continue;
        }
        let mut formals = Vec::new();
        let mut sorts = Vec::new();
        let mut formal_names = std::collections::HashSet::new();
        for parameter in parameters {
            let Some([formal, sort]) = parameter.as_list() else {
                return Err("invalid published formal parameter");
            };
            let formal_name = formal.as_symbol().ok_or("invalid published formal name")?;
            if !formal_names.insert(formal_name) {
                return Err("duplicate published formal name");
            }
            formals.push(format!("{formal}: {sort}"));
            sorts.push(sort.to_string());
        }
        bindings.push(CounterexampleBinding {
            display_name: meta.display_name,
            raw_name: name.to_string(),
            ty: format!("fn({}) -> {result}", sorts.join(", ")),
            value: format!("({}) => {body}", formals.join(", ")),
        });
    }
    bindings.sort_by(|a, b| {
        a.display_name
            .cmp(&b.display_name)
            .then_with(|| a.raw_name.cmp(&b.raw_name))
    });
    Ok(bindings)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn function_witness_retains_parameter_order_sorts_and_exact_body() {
        let model = "(model (define-fun scalar () Int 9)
            (define-fun f ((x Int) (y Int)) Int (+ y 3))
            (define-fun |quoted function| ((|formal name| Bool)) Bool (not |formal name|)))";
        let bindings = published_function_bindings(model, &HashMap::new()).unwrap();
        assert_eq!(bindings.len(), 2);
        let f = bindings
            .iter()
            .find(|binding| binding.raw_name == "f")
            .unwrap();
        assert_eq!(f.ty, "fn(Int, Int) -> Int");
        assert_eq!(f.value, "(x: Int, y: Int) => (+ y 3)");
        let quoted = bindings
            .iter()
            .find(|binding| binding.raw_name == "quoted function")
            .unwrap();
        assert!(quoted.value.contains("|formal name|"));
        assert!(!bindings.iter().any(|binding| binding.raw_name == "scalar"));
    }

    #[test]
    fn malformed_ambiguous_or_excessive_function_models_supply_no_bindings() {
        for model in [
            "(model (define-fun f ((x Int)) Int))",
            "(model (define-fun f ((x Int)) Int x) (define-fun f ((y Int)) Int 0))",
            "(error \"no model\")",
        ] {
            assert!(published_function_bindings(model, &HashMap::new()).is_err());
        }
        let too_deep = format!(
            "{}x{}",
            "(".repeat(MAX_MODEL_DEPTH + 2),
            ")".repeat(MAX_MODEL_DEPTH + 2)
        );
        assert!(published_function_bindings(&too_deep, &HashMap::new()).is_err());
        assert!(
            published_function_bindings(&" ".repeat(MAX_MODEL_BYTES + 1), &HashMap::new()).is_err()
        );
    }
}
