//! Tests for recursion detection and SCC analysis.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use crate::mode_index::{self, CanonicalFnPath};

use super::{
    clear_call_graph_cache, determine_module_path, summary_for_canonical, tarjan::tarjan_sccs,
    CrateCallGraph,
};

fn make_graph(edges: &[(&[&str], &[&[&str]])]) -> CrateCallGraph {
    let mut graph_edges = HashMap::new();
    for (caller, callees) in edges {
        let caller_path = CanonicalFnPath(caller.iter().map(|s| s.to_string()).collect());
        let callee_set: HashSet<CanonicalFnPath> = callees
            .iter()
            .map(|c| CanonicalFnPath(c.iter().map(|s| s.to_string()).collect()))
            .collect();
        graph_edges.insert(caller_path, callee_set);
    }
    CrateCallGraph { edges: graph_edges }
}

fn canonical(segments: &[&str]) -> CanonicalFnPath {
    CanonicalFnPath(segments.iter().map(|s| s.to_string()).collect())
}

#[test]
fn test_self_recursion_detected() {
    // f calls f
    let graph = make_graph(&[(&["f"], &[&["f"]])]);
    let sccs = tarjan_sccs(&graph);

    let f = canonical(&["f"]);
    let f_scc = sccs.iter().find(|scc| scc.contains(&f)).unwrap();
    assert_eq!(f_scc.len(), 1);
    // Self-loop: f is in a 1-element SCC but calls itself.
    assert!(graph.edges[&f].contains(&f));
}

#[test]
fn test_mutual_recursion_two_functions() {
    // is_even calls is_odd, is_odd calls is_even
    let graph = make_graph(&[
        (&["is_even"], &[&["is_odd"]]),
        (&["is_odd"], &[&["is_even"]]),
    ]);
    let sccs = tarjan_sccs(&graph);

    let even = canonical(&["is_even"]);
    let odd = canonical(&["is_odd"]);
    let scc = sccs.iter().find(|scc| scc.contains(&even)).unwrap();
    assert!(
        scc.contains(&odd),
        "is_even and is_odd should be in same SCC"
    );
    assert_eq!(scc.len(), 2);
}

#[test]
fn test_acyclic_not_recursive() {
    // f calls g, g calls h, no cycles
    let graph = make_graph(&[(&["f"], &[&["g"]]), (&["g"], &[&["h"]]), (&["h"], &[])]);
    let sccs = tarjan_sccs(&graph);

    // Each function is in its own 1-element SCC with no self-loop.
    for scc in &sccs {
        assert_eq!(scc.len(), 1);
    }
    let f = canonical(&["f"]);
    assert!(!graph.edges[&f].contains(&f));
}

#[test]
fn test_qualified_paths_in_scc() {
    // m::is_even calls m::is_odd, m::is_odd calls m::is_even
    let graph = make_graph(&[
        (&["m", "is_even"], &[&["m", "is_odd"]]),
        (&["m", "is_odd"], &[&["m", "is_even"]]),
    ]);
    let sccs = tarjan_sccs(&graph);

    let even = canonical(&["m", "is_even"]);
    let odd = canonical(&["m", "is_odd"]);
    let scc = sccs.iter().find(|scc| scc.contains(&even)).unwrap();
    assert!(scc.contains(&odd));
    assert_eq!(scc.len(), 2);
}

#[test]
fn test_three_function_scc() {
    // f -> g -> h -> f (cycle of 3)
    let graph = make_graph(&[
        (&["f"], &[&["g"]]),
        (&["g"], &[&["h"]]),
        (&["h"], &[&["f"]]),
    ]);
    let sccs = tarjan_sccs(&graph);

    let f = canonical(&["f"]);
    let g = canonical(&["g"]);
    let h = canonical(&["h"]);
    let scc = sccs.iter().find(|scc| scc.contains(&f)).unwrap();
    assert!(scc.contains(&g));
    assert!(scc.contains(&h));
    assert_eq!(scc.len(), 3);
}

#[test]
fn test_summary_for_canonical_mutual() {
    use std::fs;

    let dir = std::env::temp_dir()
        .join("trust_vc_recursion_graph_tests")
        .join("mutual");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();

    let root = dir.join("lib.rs");
    fs::write(
        &root,
        r#"
fn is_even(n: u32) -> bool {
    if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n: u32) -> bool {
    if n == 0 { false } else { is_even(n - 1) }
}
"#,
    )
    .unwrap();

    mode_index::clear_cache();
    clear_call_graph_cache();

    let index = mode_index::get_or_build_index(&root).unwrap();
    let even = CanonicalFnPath(vec!["is_even".to_string()]);
    let summary = summary_for_canonical(&even, &root, &index).unwrap();

    assert!(summary.is_recursive, "is_even should be recursive");
    assert!(
        summary
            .scc_members
            .contains(&CanonicalFnPath(vec!["is_odd".to_string()])),
        "is_odd should be in the same SCC"
    );
    assert_eq!(summary.scc_members.len(), 2);
}

#[test]
fn test_summary_for_canonical_self_recursive() {
    use std::fs;

    let dir = std::env::temp_dir()
        .join("trust_vc_recursion_graph_tests")
        .join("self_rec");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();

    let root = dir.join("lib.rs");
    fs::write(
        &root,
        r#"
fn factorial(n: u32) -> u32 {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}
"#,
    )
    .unwrap();

    mode_index::clear_cache();
    clear_call_graph_cache();

    let index = mode_index::get_or_build_index(&root).unwrap();
    let fact = CanonicalFnPath(vec!["factorial".to_string()]);
    let summary = summary_for_canonical(&fact, &root, &index).unwrap();

    assert!(summary.is_recursive, "factorial should be self-recursive");
}

#[test]
fn test_summary_for_canonical_not_recursive() {
    use std::fs;

    let dir = std::env::temp_dir()
        .join("trust_vc_recursion_graph_tests")
        .join("not_rec");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();

    let root = dir.join("lib.rs");
    fs::write(
        &root,
        r#"
fn double(n: u32) -> u32 {
    n * 2
}

fn quadruple(n: u32) -> u32 {
    double(double(n))
}
"#,
    )
    .unwrap();

    mode_index::clear_cache();
    clear_call_graph_cache();

    let index = mode_index::get_or_build_index(&root).unwrap();
    let dbl = CanonicalFnPath(vec!["double".to_string()]);
    let summary = summary_for_canonical(&dbl, &root, &index).unwrap();

    assert!(!summary.is_recursive, "double should not be recursive");
}

#[test]
fn test_summary_qualified_self_call() {
    use std::fs;

    let dir = std::env::temp_dir()
        .join("trust_vc_recursion_graph_tests")
        .join("qualified_self");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();

    let root = dir.join("lib.rs");
    fs::write(
        &root,
        r#"
mod m {
    fn is_even(n: u32) -> bool {
        if n == 0 { true } else { self::is_odd(n - 1) }
    }

    fn is_odd(n: u32) -> bool {
        if n == 0 { false } else { self::is_even(n - 1) }
    }
}
"#,
    )
    .unwrap();

    mode_index::clear_cache();
    clear_call_graph_cache();

    let index = mode_index::get_or_build_index(&root).unwrap();
    let even = CanonicalFnPath(vec!["m".to_string(), "is_even".to_string()]);
    let summary = summary_for_canonical(&even, &root, &index).unwrap();

    assert!(
        summary.is_recursive,
        "m::is_even with self::is_odd call should be recursive"
    );
    assert!(summary.scc_members.contains(&CanonicalFnPath(vec![
        "m".to_string(),
        "is_odd".to_string()
    ])));
}

#[test]
fn test_determine_module_path_root() {
    use std::fs;

    let dir = std::env::temp_dir()
        .join("trust_vc_recursion_graph_tests")
        .join("mod_path");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();

    let root = dir.join("lib.rs");
    fs::write(&root, "").unwrap();

    let result = determine_module_path(&root, &root);
    assert!(result.is_empty(), "root file should have empty module path");
}

#[test]
fn test_determine_module_path_submodule() {
    use std::fs;

    let dir = std::env::temp_dir()
        .join("trust_vc_recursion_graph_tests")
        .join("mod_path_sub");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(dir.join("specs")).unwrap();

    let root = dir.join("lib.rs");
    fs::write(&root, "").unwrap();
    let sub = dir.join("specs").join("helpers.rs");
    fs::write(&sub, "").unwrap();

    let result = determine_module_path(&sub, &root);
    assert_eq!(result, vec!["specs", "helpers"]);
}

/// #2550 F1: impl method self-recursion should be detected.
#[test]
fn test_impl_method_self_recursion_detected() {
    use std::fs;

    let dir = std::env::temp_dir()
        .join("trust_vc_recursion_graph_tests")
        .join("impl_self_rec");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();

    let root = dir.join("lib.rs");
    fs::write(
        &root,
        r#"
struct Tree {
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

impl Tree {
    fn count(&self) -> u64 {
        1 + self.left.as_ref().map_or(0, |l| l.count())
            + self.right.as_ref().map_or(0, |r| r.count())
    }
}
"#,
    )
    .unwrap();

    mode_index::clear_cache();
    clear_call_graph_cache();

    let index = mode_index::get_or_build_index(&root).unwrap();

    // Verify impl method is in the index with type-scoped path.
    let count_path = CanonicalFnPath(vec!["Tree".to_string(), "count".to_string()]);
    assert!(
        index.lookup(&count_path).is_some(),
        "Tree::count should be in the index"
    );

    // Verify self-recursion: count calls count (via method call).
    let summary = summary_for_canonical(&count_path, &root, &index).unwrap();
    assert!(
        summary.is_recursive,
        "Tree::count should be detected as self-recursive"
    );
}

/// #2550 F1: impl method mutual recursion across impl blocks.
#[test]
fn test_impl_method_in_call_graph() {
    use std::fs;

    let dir = std::env::temp_dir()
        .join("trust_vc_recursion_graph_tests")
        .join("impl_call_graph");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();

    let root = dir.join("lib.rs");
    fs::write(
        &root,
        r#"
struct Foo;

impl Foo {
    fn bar(&self) -> u64 {
        self.baz()
    }

    fn baz(&self) -> u64 {
        self.bar()
    }
}
"#,
    )
    .unwrap();

    mode_index::clear_cache();
    clear_call_graph_cache();

    let index = mode_index::get_or_build_index(&root).unwrap();

    let bar_path = CanonicalFnPath(vec!["Foo".to_string(), "bar".to_string()]);
    let baz_path = CanonicalFnPath(vec!["Foo".to_string(), "baz".to_string()]);
    assert!(
        index.lookup(&bar_path).is_some(),
        "Foo::bar should be indexed"
    );
    assert!(
        index.lookup(&baz_path).is_some(),
        "Foo::baz should be indexed"
    );

    let summary = summary_for_canonical(&bar_path, &root, &index).unwrap();
    assert!(
        summary.is_recursive,
        "Foo::bar and Foo::baz should form a mutual recursion SCC"
    );
    assert!(
        summary.scc_members.contains(&baz_path),
        "Foo::baz should be in the same SCC as Foo::bar"
    );
}
