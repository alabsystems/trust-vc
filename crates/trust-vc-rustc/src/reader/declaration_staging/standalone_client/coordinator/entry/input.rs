// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict typed interpretation of plain launch data, never a saved owner.

use super::*;
use serde_json::{Map, Value};

pub(super) struct Frontend {
    pub(super) name: String,
    pub(super) path: PathBuf,
    pub(super) sha256: [u8; 32],
}

pub(super) struct RunnerInput {
    pub(super) program: PathBuf,
    pub(super) arguments: Vec<String>,
    pub(super) cwd: PathBuf,
}

pub(super) struct Input {
    pub(super) schema: String,
    pub(super) producer_request: PathBuf,
    pub(super) sdk: PathBuf,
    pub(super) frontends: Vec<Frontend>,
    pub(super) runner: RunnerInput,
}

fn object(value: Value, fields: &[&str]) -> Result<Map<String, Value>, String> {
    let Value::Object(map) = value else {
        return Err("the coordinator input requires an object".into());
    };
    if map.len() != fields.len() || map.keys().any(|key| !fields.contains(&key.as_str())) {
        return Err("the coordinator input has missing or unrepresented fields".into());
    }
    Ok(map)
}

fn text(map: &mut Map<String, Value>, name: &str) -> Result<String, String> {
    match map.remove(name) {
        Some(Value::String(value)) => Ok(value),
        _ => Err(format!("the coordinator {name} must be a string")),
    }
}

impl Input {
    pub(super) fn parse(value: Value) -> Result<Self, String> {
        let mut map = object(
            value,
            &["schema", "producer_request", "sdk", "frontends", "runner"],
        )?;
        let schema = text(&mut map, "schema")?;
        let producer_request = text(&mut map, "producer_request")?.into();
        let sdk = text(&mut map, "sdk")?.into();
        let Value::Array(items) = map.remove("frontends").unwrap() else {
            return Err("the coordinator frontends must be an array".into());
        };
        let frontends = items
            .into_iter()
            .map(|value| {
                let mut map = object(value, &["name", "path", "sha256"])?;
                Ok(Frontend {
                    name: text(&mut map, "name")?,
                    path: text(&mut map, "path")?.into(),
                    sha256: serde_json::from_value(map.remove("sha256").unwrap())
                        .map_err(|error| format!("invalid frontend SHA-256: {error}"))?,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let mut runner = object(
            map.remove("runner").unwrap(),
            &["program", "arguments", "cwd"],
        )?;
        let runner = RunnerInput {
            program: text(&mut runner, "program")?.into(),
            cwd: text(&mut runner, "cwd")?.into(),
            arguments: serde_json::from_value(runner.remove("arguments").unwrap())
                .map_err(|error| format!("invalid runner arguments: {error}"))?,
        };
        Ok(Self {
            schema,
            producer_request,
            sdk,
            frontends,
            runner,
        })
    }
}
