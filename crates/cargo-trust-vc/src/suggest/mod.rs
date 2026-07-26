// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Oracle-driven specification suggestion for Rust functions.

use std::fmt::Write as FmtWrite;
use std::path::{Path, PathBuf};

use clap::Parser;
use thiserror::Error;
use trust_vc_oracle::{
    run_oracle, try_parse_functions, ClaudeBackend, CodexBackend, FunctionSignature, LlmBackend,
    MockBackend, OracleConfig, OracleError, OracleResult, ProposedAnnotations,
};

const DEFAULT_CODEX_MODEL: &str = "o4-mini";
const DEFAULT_CLAUDE_MODEL: &str = "sonnet";

#[derive(Debug, Clone, Parser)]
#[command(
    bin_name = "cargo trust_vc suggest",
    about = "Suggest trust_vc annotations by running the oracle on a Rust file or function."
)]
pub(crate) struct SuggestArgs {
    /// Rust source file to analyze.
    #[arg(long, value_name = "PATH")]
    pub(crate) file: PathBuf,

    /// Specific function to target. When omitted, all functions in the file are analyzed.
    #[arg(long, value_name = "NAME")]
    pub(crate) function: Option<String>,

    /// LLM backend to use.
    #[arg(long, value_name = "BACKEND")]
    pub(crate) backend: BackendKind,

    /// Model identifier for the selected backend.
    #[arg(long, value_name = "MODEL")]
    pub(crate) model: Option<String>,

    /// Maximum oracle iteration budget.
    #[arg(long, value_name = "N", default_value_t = 5, value_parser = parse_max_iterations)]
    pub(crate) max_iterations: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum BackendKind {
    Codex,
    Claude,
    #[value(hide = true)]
    Mock,
}

#[derive(Debug, Error)]
pub(crate) enum SuggestError {
    #[error("cannot read {path}: {source}")]
    ReadSource {
        path: String,
        #[source]
        source: std::io::Error,
    },

    #[error("cannot parse {path}: {source}")]
    ParseSource {
        path: String,
        #[source]
        source: OracleError,
    },

    #[error("no functions found in {path}")]
    NoFunctionsFound { path: String },

    #[error("no function named '{name}' found in {path}")]
    FunctionNotFound { path: String, name: String },

    #[error("oracle failed for function '{function}': {source}")]
    OracleRun {
        function: String,
        #[source]
        source: OracleError,
    },
}

pub(crate) fn detect_suggest_subcommand(
    raw_args: &[String],
) -> Result<Option<SuggestArgs>, clap::Error> {
    let suggest_pos = match raw_args {
        [_, cmd, ..] if cmd == "suggest" => Some(1),
        [_, cargo, cmd, ..] if cargo == "trust_vc" && cmd == "suggest" => Some(2),
        [_, cargo, check, cmd, ..]
            if cargo == "trust_vc" && check == "check" && cmd == "suggest" =>
        {
            Some(3)
        }
        _ => None,
    };

    let Some(suggest_pos) = suggest_pos else {
        return Ok(None);
    };

    let synthetic_args: Vec<String> = std::iter::once(raw_args[0].clone())
        .chain(raw_args[suggest_pos + 1..].iter().cloned())
        .collect();

    SuggestArgs::try_parse_from(synthetic_args).map(Some)
}

pub(crate) fn run_suggest(args: &SuggestArgs) -> Result<String, SuggestError> {
    let source =
        std::fs::read_to_string(&args.file).map_err(|source| SuggestError::ReadSource {
            path: display_path(&args.file),
            source,
        })?;
    let functions = try_parse_functions(&source).map_err(|source| SuggestError::ParseSource {
        path: display_path(&args.file),
        source,
    })?;
    let targets = select_targets(&functions, &args.file, args.function.as_deref())?;
    let backend = build_backend(args.backend, args.model.as_deref(), &args.file);
    let config = OracleConfig {
        max_iterations: args.max_iterations,
        verbose: false,
    };

    let mut output = String::new();
    for (index, function) in targets.iter().enumerate() {
        let result = run_oracle(function, backend.as_ref(), &config).map_err(|source| {
            SuggestError::OracleRun {
                function: function.name.clone(),
                source,
            }
        })?;
        if index > 0 {
            output.push('\n');
        }
        render_result(&mut output, function, &result);
    }

    Ok(output)
}

fn select_targets<'a>(
    functions: &'a [FunctionSignature],
    file: &Path,
    function_name: Option<&str>,
) -> Result<Vec<&'a FunctionSignature>, SuggestError> {
    if let Some(name) = function_name {
        let function = functions
            .iter()
            .find(|function| function.name == name)
            .ok_or_else(|| SuggestError::FunctionNotFound {
                path: display_path(file),
                name: name.to_owned(),
            })?;
        return Ok(vec![function]);
    }

    if functions.is_empty() {
        return Err(SuggestError::NoFunctionsFound {
            path: display_path(file),
        });
    }

    Ok(functions.iter().collect())
}

fn build_backend(backend: BackendKind, model: Option<&str>, file: &Path) -> Box<dyn LlmBackend> {
    match backend {
        BackendKind::Codex => {
            let model = resolve_model(backend, model);
            let backend = file
                .parent()
                .and_then(Path::to_str)
                .map(|dir| CodexBackend::new(&model).with_working_dir(dir))
                .unwrap_or_else(|| CodexBackend::new(&model));
            Box::new(backend)
        }
        BackendKind::Claude => Box::new(ClaudeBackend::new(&resolve_model(backend, model))),
        BackendKind::Mock => Box::new(MockBackend::new(vec![trivial_proposal()])),
    }
}

fn resolve_model(backend: BackendKind, model: Option<&str>) -> String {
    model
        .unwrap_or(match backend {
            BackendKind::Codex => DEFAULT_CODEX_MODEL,
            BackendKind::Claude => DEFAULT_CLAUDE_MODEL,
            BackendKind::Mock => "mock",
        })
        .to_owned()
}

fn trivial_proposal() -> ProposedAnnotations {
    ProposedAnnotations {
        requires: Vec::new(),
        ensures: Vec::new(),
        invariants: Vec::new(),
        decreases: Vec::new(),
        raw_response: String::new(),
    }
}

fn render_result(output: &mut String, function: &FunctionSignature, result: &OracleResult) {
    let params = function
        .params
        .iter()
        .map(|(name, ty)| format!("{name}: {ty}"))
        .collect::<Vec<_>>()
        .join(", ");
    let return_type = function
        .return_type
        .as_deref()
        .map_or(String::new(), |ty| format!(" -> {ty}"));

    let _ = writeln!(
        output,
        "--- fn {}({}){} ---",
        function.name, params, return_type
    );
    let _ = writeln!(
        output,
        "Status: {}",
        if result.is_verified() {
            "VERIFIED"
        } else {
            "NOT VERIFIED"
        }
    );
    let _ = writeln!(output, "Iterations: {}", result.iterations);

    if let Some(annotations) = &result.annotations {
        append_annotations(output, annotations);
    } else {
        for line in result.final_feedback.to_llm_summary().lines() {
            let _ = writeln!(output, "{line}");
        }
    }
}

fn append_annotations(output: &mut String, annotations: &ProposedAnnotations) {
    if annotations.requires.is_empty()
        && annotations.ensures.is_empty()
        && annotations.invariants.is_empty()
        && annotations.decreases.is_empty()
    {
        let _ = writeln!(output, "No annotations proposed.");
        return;
    }

    for require in &annotations.requires {
        let _ = writeln!(output, "requires!({require});");
    }
    for ensure in &annotations.ensures {
        let _ = writeln!(output, "ensures!({ensure});");
    }
    for (label, invariant) in &annotations.invariants {
        let _ = writeln!(output, "invariant!({label}: {invariant});");
    }
    for decreases in &annotations.decreases {
        let _ = writeln!(output, "decreases!({decreases});");
    }
}

fn display_path(path: &Path) -> String {
    path.display().to_string()
}

fn parse_max_iterations(value: &str) -> Result<usize, String> {
    let parsed = value
        .parse::<usize>()
        .map_err(|_| format!("invalid integer '{value}'"))?;
    if parsed == 0 {
        return Err("max iterations must be at least 1".to_owned());
    }
    Ok(parsed)
}

#[cfg(test)]
mod tests;
