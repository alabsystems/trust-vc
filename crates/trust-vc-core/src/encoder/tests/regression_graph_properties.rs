// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn handshaking_lemma_simple() {
    // Sum of degrees = 2 * edges (for undirected graph)
    // Triangle: 3 vertices, 3 edges, each vertex degree 2, sum = 6
    let mut ctx = VerificationContext::new();
    for v in &["d0", "d1", "d2", "sum_degrees", "edges", "double_edges"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("d0_val", "d0 == 2"));
    ctx.push_obligation(ProofObligation::assume("d1_val", "d1 == 2"));
    ctx.push_obligation(ProofObligation::assume("d2_val", "d2 == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sum_def",
        "sum_degrees == d0 + d1 + d2",
    ));
    ctx.push_obligation(ProofObligation::assume("edges_val", "edges == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "double_def",
        "double_edges == edges + edges",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "handshaking",
        "sum_degrees == double_edges",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "triangle: sum(degrees) = 2 * edges");
}

#[test]
fn complete_graph_edges() {
    // K_n has n*(n-1)/2 edges; K_4 has 6
    let mut ctx = VerificationContext::new();
    for v in &["n", "edges"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "edges_def",
        "edges == n * (n - 1) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "edges == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "K_4 has 6 edges");
}

#[test]
fn tree_edges_count() {
    // A tree with n vertices has n-1 edges
    let mut ctx = VerificationContext::new();
    for v in &["vertices", "edges"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v_val", "vertices == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "edges_def",
        "edges == vertices - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_6", "edges == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tree with 7 vertices has 6 edges");
}

#[test]
fn adjacency_matrix_symmetric() {
    // For undirected graph, adj[i][j] == adj[j][i]
    let mut ctx = VerificationContext::new();
    for v in &["a_ij", "a_ji"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("aij", "a_ij == 1"));
    ctx.push_obligation(ProofObligation::assume("aji_def", "a_ji == a_ij"));
    ctx.push_obligation(ProofObligation::assert("symmetric", "a_ij == a_ji"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "undirected: adj[i][j] == adj[j][i]");
}

#[test]
fn vertex_degree_from_adjacency() {
    // Degree of vertex 0 in triangle: adj[0][1] + adj[0][2] = 2
    let mut ctx = VerificationContext::new();
    for v in &["a01", "a02", "degree0"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a01_val", "a01 == 1"));
    ctx.push_obligation(ProofObligation::assume("a02_val", "a02 == 1"));
    ctx.push_obligation(ProofObligation::assume("deg_def", "degree0 == a01 + a02"));
    ctx.push_obligation(ProofObligation::assert("is_2", "degree0 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "triangle vertex has degree 2");
}

#[test]
fn path_length() {
    // Path from v0 → v1 → v2 → v3 has 3 edges
    let mut ctx = VerificationContext::new();
    for v in &["vertices_in_path", "path_edges"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("vip", "vertices_in_path == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "pe_def",
        "path_edges == vertices_in_path - 1",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "path_edges == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "path through 4 vertices has 3 edges");
}

#[test]
fn bipartite_max_edges() {
    // Complete bipartite K_{m,n} has m*n edges
    let mut ctx = VerificationContext::new();
    for v in &["m", "n", "edges"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("m_val", "m == 3"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 4"));
    ctx.push_obligation(ProofObligation::assume("edges_def", "edges == m * n"));
    ctx.push_obligation(ProofObligation::assert("is_12", "edges == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "K_{3,4} has 12 edges");
}

#[test]
fn cycle_graph_edges() {
    // Cycle C_n has n edges
    let mut ctx = VerificationContext::new();
    for v in &["vertices", "edges"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v_val", "vertices == 5"));
    ctx.push_obligation(ProofObligation::assume("edges_def", "edges == vertices"));
    ctx.push_obligation(ProofObligation::assert("is_5", "edges == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "C_5 has 5 edges");
}

#[test]
fn in_degree_plus_out_degree() {
    // For directed graph, total degree = in_degree + out_degree
    let mut ctx = VerificationContext::new();
    for v in &["in_deg", "out_deg", "total_deg"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("in_val", "in_deg == 3"));
    ctx.push_obligation(ProofObligation::assume("out_val", "out_deg == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total_deg == in_deg + out_deg",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "total_deg == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total degree = in(3) + out(2) = 5");
}

#[test]
fn euler_formula_planar() {
    // For connected planar graph: V - E + F = 2
    let mut ctx = VerificationContext::new();
    for v in &["vertices", "edges", "faces", "euler"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Tetrahedron: V=4, E=6, F=4
    ctx.push_obligation(ProofObligation::assume("v_val", "vertices == 4"));
    ctx.push_obligation(ProofObligation::assume("e_val", "edges == 6"));
    ctx.push_obligation(ProofObligation::assume("f_val", "faces == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "euler_def",
        "euler == vertices - edges + faces",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "euler == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Euler formula: 4 - 6 + 4 = 2");
}
