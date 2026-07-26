// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use clap::{CommandFactory, ValueEnum};
use std::io::Write;

fn write_temp_source(label: &str, source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_vc_suggest_{label}_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after UNIX_EPOCH")
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).expect("temp dir should be creatable");
    let path = dir.join("test.rs");
    let mut file = std::fs::File::create(&path).expect("temp source should be creatable");
    file.write_all(source.as_bytes())
        .expect("temp source should be writable");
    path
}

fn backend_name(kind: BackendKind) -> String {
    kind.to_possible_value()
        .expect("public backend should have a clap value")
        .get_name()
        .to_string()
}

#[test]
fn detect_suggest_subcommand_parses_cargo_trust_vc_style() {
    let raw_args = vec![
        "cargo-trust-vc".to_string(),
        "suggest".to_string(),
        "--file".to_string(),
        "src/lib.rs".to_string(),
        "--backend".to_string(),
        backend_name(BackendKind::Codex),
        "--model".to_string(),
        "gpt-5".to_string(),
    ];

    let args = detect_suggest_subcommand(&raw_args)
        .expect("suggest args should parse")
        .expect("suggest subcommand should be detected");

    assert_eq!(args.file, PathBuf::from("src/lib.rs"));
    assert_eq!(args.backend, BackendKind::Codex);
    assert_eq!(args.model.as_deref(), Some("gpt-5"));
}

#[test]
fn detect_suggest_subcommand_parses_cargo_space_trust_vc_style() {
    let raw_args = vec![
        "cargo".to_string(),
        "trust_vc".to_string(),
        "suggest".to_string(),
        "--file".to_string(),
        "src/lib.rs".to_string(),
        "--backend".to_string(),
        backend_name(BackendKind::Claude),
    ];

    let args = detect_suggest_subcommand(&raw_args)
        .expect("suggest args should parse")
        .expect("suggest subcommand should be detected");

    assert_eq!(args.backend, BackendKind::Claude);
    assert_eq!(args.max_iterations, 5);
}

#[test]
fn detect_suggest_subcommand_returns_error_for_invalid_backend() {
    let raw_args = vec![
        "cargo-trust-vc".to_string(),
        "suggest".to_string(),
        "--file".to_string(),
        "src/lib.rs".to_string(),
        "--backend".to_string(),
        "invalid".to_string(),
    ];

    let error = detect_suggest_subcommand(&raw_args).expect_err("backend should be rejected");
    let rendered = error.to_string();

    assert!(rendered.contains("invalid value"));
}

#[test]
fn suggest_help_lists_only_public_backends() {
    let help = SuggestArgs::command().render_long_help().to_string();
    let codex = backend_name(BackendKind::Codex);
    let claude = backend_name(BackendKind::Claude);

    assert!(help.contains(&codex));
    assert!(help.contains(&claude));
    assert!(!help.contains("mock"));
}

#[test]
fn resolve_model_uses_backend_defaults() {
    assert_eq!(resolve_model(BackendKind::Codex, None), DEFAULT_CODEX_MODEL);
    assert_eq!(
        resolve_model(BackendKind::Claude, None),
        DEFAULT_CLAUDE_MODEL
    );
}

#[test]
fn resolve_model_prefers_override() {
    assert_eq!(
        resolve_model(BackendKind::Codex, Some("custom-model-a")),
        "custom-model-a"
    );
    assert_eq!(
        resolve_model(BackendKind::Claude, Some("custom-model-b")),
        "custom-model-b"
    );
}

#[test]
fn run_suggest_filters_to_named_function() {
    let path = write_temp_source(
        "named_fn",
        "fn alpha(x: u32) -> u32 { x }\nfn beta(x: u32) -> u32 { x + 1 }\n",
    );
    let args = SuggestArgs {
        file: path.clone(),
        function: Some("beta".to_string()),
        backend: BackendKind::Mock,
        model: None,
        max_iterations: 3,
    };

    let output = run_suggest(&args).expect("mock backend should succeed");

    assert!(output.contains("--- fn beta(x: u32) -> u32 ---"));
    assert!(!output.contains("--- fn alpha(x: u32) -> u32 ---"));

    std::fs::remove_dir_all(path.parent().expect("temp dir should exist")).ok();
}

#[test]
fn run_suggest_errors_when_file_has_no_functions() {
    let path = write_temp_source("empty", "");
    let args = SuggestArgs {
        file: path.clone(),
        function: None,
        backend: BackendKind::Mock,
        model: None,
        max_iterations: 3,
    };

    let error = run_suggest(&args).expect_err("empty file should be rejected");

    assert!(matches!(error, SuggestError::NoFunctionsFound { .. }));

    std::fs::remove_dir_all(path.parent().expect("temp dir should exist")).ok();
}

#[test]
fn run_suggest_surfaces_parse_errors() {
    let path = write_temp_source("invalid", "fn broken(");
    let args = SuggestArgs {
        file: path.clone(),
        function: None,
        backend: BackendKind::Mock,
        model: None,
        max_iterations: 3,
    };

    let error = run_suggest(&args).expect_err("invalid source should fail");

    assert!(matches!(error, SuggestError::ParseSource { .. }));

    std::fs::remove_dir_all(path.parent().expect("temp dir should exist")).ok();
}
