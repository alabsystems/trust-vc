// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Genuine ordinary helper compilation and exact compiler outcome oracles.
use super::*;

fn client(case: Case) -> String {
    let (signature, body) = match case {
        Case::Moved | Case::FullKeep | Case::Unrelated => ("fn target<T>(original: T)",
            "let kept = original; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original; } kept;"),
        Case::ExecMove => ("fn target<T>(original: T)", "original; original;"),
        Case::ErasedReads => ("fn target<T>(original: T)",
            "#[verifier::proof_block] { #[verus::internal(spec)] let ghost = original; #[verus::internal(spec)] let first = ghost; #[verus::internal(spec)] let second = ghost; } original;"),
        Case::LastRead => ("fn target(mut original: u64)",
            "let loan = &mut original; *loan = 7; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original; }"),
        Case::FutureRead => ("fn target(mut original: u64)",
            "let loan = &mut original; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original; } *loan = 7;"),
        Case::ExecBorrow => ("fn target(mut original: u64)",
            "let first = &mut original; let second = &mut original; *first = 1; *second = 2;"),
        Case::Reset => ("fn target(mut first: u64, mut second: u64)",
            "let mut r = &mut first; let p = &mut *r; r = &mut second; let q = &mut *r; *p = 1; *q = 2;"),
        Case::ResetOrder => ("fn target(mut first: u64, mut second: u64)",
            "let mut r = &mut first; let p = &mut *r; r = { #[verifier::proof_block] { #[verus::internal(spec)] let observed = *r; } &mut second }; *p = 1;"),
        Case::ImplicitLastRead => ("fn target(mut original: u64)",
            "let mut r = &mut original; let p: &mut u64 = r; *p = 7; #[verifier::proof_block] { #[verus::internal(spec)] let observed = *r; }"),
        Case::ImplicitFutureRead => ("fn target(mut original: u64)",
            "let mut r = &mut original; let p: &mut u64 = r; #[verifier::proof_block] { #[verus::internal(spec)] let observed = *r; } *p = 7;"),
        Case::ImplicitProof => ("fn target(mut original: u64)",
            "#[verifier::proof_block] { #[verus::internal(proof)] let r = &mut original; #[verus::internal(proof)] let p: &mut u64 = r; p; }"),
        Case::Projected(case) => projections::source(case),
    };
    let declarations = if let Case::Projected(case) = case {
        projections::declarations(case)
    } else {
        ""
    };
    let unrelated = if case == Case::Unrelated {
        "fn untouched<T>(value: T) { value; value; }"
    } else {
        ""
    };
    format!("#![feature(register_tool, stmt_expr_attributes)]\n#![register_tool(verus)]\n#![register_tool(verifier)]\n#![allow(dead_code, unused_variables, unused_mut, path_statements)]\n{declarations}macro_rules! make_target {{ () => {{ #[verus::internal(verus_macro)] #[verus::internal(exec)] {signature} {{ {body} }} }}; }}\nmake_target!();\nfn helper_anchor() {{ allocation_helper::erased::<(),u8>(()); allocation_helper::shadow::<(),u8>(()); let mut a=0u8; let mut b=0u16; allocation_helper::tie(&mut a,&mut b); }}\n{unrelated}\n")
}

struct Emit;
impl Callbacks for Emit {}
fn args(input: &std::path::Path, output: &std::path::Path, name: &str) -> Vec<String> {
    vec![
        "native-shadow-availability-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        format!("--crate-name={name}"),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        output.to_str().unwrap().into(),
        input.to_str().unwrap().into(),
    ]
}
pub(super) fn run(case: Case) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-shadow-availability-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let foreign = directory.0.join("helpers.rs");
    std::fs::write(&foreign, "pub fn erased<S,T>(_:S)->T { loop{} }\npub fn shadow<S,T>(_:S)->T { loop{} }\npub fn tie<'a,T:?Sized,U:?Sized>(value:&'a mut T,_shadow:&'a mut U)->&'a mut T { value }\n").unwrap();
    assert!(
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(
            &args(&foreign, &directory.0, "allocation_helper"),
            &mut Emit
        ))
        .is_ok()
    );
    let input = directory.0.join("client.rs");
    std::fs::write(&input, client(case)).unwrap();
    let mut arguments = args(&input, &directory.0, "shadow_availability_client");
    arguments.extend([
        "--extern".into(),
        format!(
            "allocation_helper={}",
            directory.0.join("liballocation_helper.rmeta").display()
        ),
    ]);
    let diagnostics = Arc::new(Mutex::new(Vec::new()));
    let mut callback = Run {
        case,
        diagnostics: Arc::clone(&diagnostics),
        reached: false,
        target_ok: None,
        roots: 0,
        analysis: false,
    };
    let result =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut callback));
    assert!(callback.reached);
    assert_eq!(callback.roots, if case == Case::Unrelated { 3 } else { 2 });
    assert_eq!(
        callback.target_ok,
        Some(case.error().is_none() || case == Case::Unrelated)
    );
    assert_eq!(result.is_err(), case.error().is_some());
    assert_eq!(callback.analysis, case.error().is_none());
    let diagnostics = diagnostics.lock().unwrap();
    let coded = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code.is_some())
        .collect::<Vec<_>>();
    if let Some(expected) = case.error() {
        assert!(!coded.is_empty(), "{diagnostics:?}");
        assert!(
            coded
                .iter()
                .all(|diagnostic| diagnostic.code.as_deref() == Some(expected)),
            "{diagnostics:?}"
        );
        assert!(coded.iter().all(|diagnostic| !diagnostic.primary.is_empty()
            && diagnostic.primary.iter().all(|span| !span.is_dummy())));
        if case == Case::ExecBorrow {
            assert!(
                coded
                    .iter()
                    .any(|diagnostic| diagnostic.detail.contains("original")),
                "the actual original borrow conflict must remain: {diagnostics:?}"
            );
        }
    } else {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }
}
