// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CLI entry point for the merge bundle runner.
//!
//! Usage: trust-vc-merge-runner <bundle_path> <obligation_id> <engine>
//!
//! Outputs a normalized JSON verdict to stdout.

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 4 {
        eprintln!(
            "Usage: {} <bundle_path> <obligation_id> <engine>",
            args.first().map_or("trust-vc-merge-runner", |s| s.as_str())
        );
        std::process::exit(1);
    }

    let bundle_path = &args[1];
    let obligation_id = &args[2];
    let engine = &args[3];

    match trust_vc_merge_runner::run_bundle_path(bundle_path, obligation_id, engine) {
        Ok(verdict) => match serde_json::to_string_pretty(&verdict) {
            Ok(json) => println!("{json}"),
            Err(e) => {
                eprintln!("Error: failed to serialize verdict JSON: {e}");
                std::process::exit(3);
            }
        },
        Err(e) => {
            eprintln!("Error: {e}");
            std::process::exit(2);
        }
    }
}
