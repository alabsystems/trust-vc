// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::program::GeneratedProgram;
use trust_vc_core::{extract_verification_conditions, VerifyResult};
use syn::{File, Item, ItemFn};

#[derive(Debug)]
pub struct VerificationOutcome {
    case: GeneratedProgram,
    result: Result<VerifyResult, String>,
}

impl VerificationOutcome {
    pub fn is_false_verified(&self) -> bool {
        matches!(self.result, Ok(VerifyResult::Verified))
    }

    pub fn assert_not_verified(&self) {
        assert!(
            !self.is_false_verified(),
            "false-Verified fuzz case in target '{}': {}\nresult: {}\nsource:\n{}",
            self.case.target_name,
            self.case.description,
            self.status(),
            self.case.source
        );
    }

    pub fn status(&self) -> String {
        match &self.result {
            Ok(result) => format!("{result:?}"),
            Err(error) => error.clone(),
        }
    }
}

pub fn verify_generated_program(case: GeneratedProgram) -> VerificationOutcome {
    let result = parse_case(&case).and_then(|parsed| {
        let function = find_function(&parsed, case.function_name)?.clone();
        extract_verification_conditions(&function)
            .map_err(|error| format!("vc extraction failed: {error}"))
            .map(|context| context.verify())
    });

    VerificationOutcome { case, result }
}

fn parse_case(case: &GeneratedProgram) -> Result<File, String> {
    syn::parse_file(&case.source).map_err(|error| format!("source parse failed: {error}"))
}

fn find_function<'a>(file: &'a File, function_name: &str) -> Result<&'a ItemFn, String> {
    file.items
        .iter()
        .find_map(|item| match item {
            Item::Fn(function) if function.sig.ident == function_name => Some(function),
            _ => None,
        })
        .ok_or_else(|| format!("function '{function_name}' not found in generated source"))
}
