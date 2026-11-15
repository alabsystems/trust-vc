// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn paths(value: &str) -> BTreeSet<PathBuf> {
    BTreeSet::from([PathBuf::from(value)])
}

fn base() -> Vec<String> {
    [
        "compiler",
        "-Ztrust-verify=off",
        "-L",
        "dependency=/native/sysroot",
        "-L",
        "dependency=/owned/original",
        "--cfg",
        "verus_keep_ghost_body",
        "--extern",
        "force:verus_builtin=/owned/original/libverus_builtin.rlib",
        "--extern",
        "force:verus_builtin_macros=/owned/copied/libverus_builtin_macros.dylib",
        "--extern",
        "force:verus_state_machines_macros=/owned/copied/libverus_state_machines_macros.dylib",
        "/client/original.rs",
        "-o",
        "/owned/client.rmeta",
    ]
    .map(String::from)
    .to_vec()
}

fn dependency_paths(args: &[String]) -> Vec<PathBuf> {
    args.windows(2)
        .filter(|pair| pair[0] == "-L")
        .map(|pair| PathBuf::from(pair[1].strip_prefix("dependency=").unwrap()))
        .collect()
}

#[test]
fn copied_recipe_has_one_macro_candidate_directory_and_preserves_nonsearch_inputs() {
    let args = base();
    let selected = selected_search(
        args.clone(),
        &paths("/owned/original"),
        &paths("/owned/copied"),
    )
    .unwrap();
    assert_eq!(
        dependency_paths(&selected),
        vec![
            PathBuf::from("/owned/copied"),
            PathBuf::from("/native/sysroot")
        ]
    );
    // Removing only search pairs yields byte-identical flags, original
    // nonmacro extern, forced macro files, original client and output.
    let without_search = |args: &[String]| {
        let mut out = Vec::new();
        let mut at = 0;
        while at < args.len() {
            if args[at] == "-L" {
                at += 2;
            } else {
                out.push(args[at].clone());
                at += 1;
            }
        }
        out
    };
    assert_eq!(without_search(&selected), without_search(&args));
    assert!(!dependency_paths(&selected).contains(&PathBuf::from("/owned/original")));
}

#[test]
fn original_recipe_keeps_its_search_paths_without_an_extra_original_append() {
    let args = base();
    assert_eq!(
        selected_search(
            args.clone(),
            &paths("/owned/original"),
            &paths("/owned/original")
        )
        .unwrap(),
        args
    );
}

#[test]
fn incomplete_or_overlapping_macro_search_inventory_refuses() {
    assert!(selected_search(base(), &paths("/not-present"), &paths("/owned/copied")).is_err());
    let mut overlapping = paths("/owned/original");
    overlapping.insert(PathBuf::from("/owned/copied"));
    assert!(selected_search(base(), &overlapping, &paths("/owned/copied")).is_err());
    assert!(selected_search(base(), &paths("/owned/original"), &BTreeSet::new()).is_err());
    let mut hidden = base();
    hidden.extend(["-L".into(), "all=/owned/original".into()]);
    assert!(selected_search(hidden, &paths("/owned/original"), &paths("/owned/copied")).is_err());
}
