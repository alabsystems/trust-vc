//! Tarjan's SCC algorithm for recursion detection.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use crate::mode_index::CanonicalFnPath;

use super::CrateCallGraph;

pub(super) struct TarjanState {
    index_counter: usize,
    stack: Vec<CanonicalFnPath>,
    on_stack: HashSet<CanonicalFnPath>,
    indices: HashMap<CanonicalFnPath, usize>,
    lowlinks: HashMap<CanonicalFnPath, usize>,
    pub sccs: Vec<HashSet<CanonicalFnPath>>,
}

pub(super) fn tarjan_sccs(graph: &CrateCallGraph) -> Vec<HashSet<CanonicalFnPath>> {
    let mut state = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: HashSet::new(),
        indices: HashMap::new(),
        lowlinks: HashMap::new(),
        sccs: Vec::new(),
    };

    for node in graph.edges.keys() {
        if !state.indices.contains_key(node) {
            strongconnect(node, graph, &mut state);
        }
    }

    state.sccs
}

fn strongconnect(v: &CanonicalFnPath, graph: &CrateCallGraph, state: &mut TarjanState) {
    let idx = state.index_counter;
    state.index_counter += 1;
    state.indices.insert(v.clone(), idx);
    state.lowlinks.insert(v.clone(), idx);
    state.stack.push(v.clone());
    state.on_stack.insert(v.clone());

    if let Some(neighbors) = graph.edges.get(v) {
        for w in neighbors {
            if !state.indices.contains_key(w) {
                // w has not been visited; recurse.
                strongconnect(w, graph, state);
                if let (Some(w_lowlink), Some(v_lowlink)) =
                    (state.lowlinks.get(w).copied(), state.lowlinks.get_mut(v))
                {
                    if w_lowlink < *v_lowlink {
                        *v_lowlink = w_lowlink;
                    }
                }
            } else if state.on_stack.contains(w) {
                // w is on the stack → it's in the current SCC.
                if let (Some(w_index), Some(v_lowlink)) =
                    (state.indices.get(w).copied(), state.lowlinks.get_mut(v))
                {
                    if w_index < *v_lowlink {
                        *v_lowlink = w_index;
                    }
                }
            }
        }
    }

    // If v is a root node, pop the SCC.
    let (Some(v_lowlink), Some(v_index)) = (state.lowlinks.get(v), state.indices.get(v)) else {
        return;
    };
    if v_lowlink == v_index {
        let mut scc = HashSet::new();
        while let Some(w) = state.stack.pop() {
            state.on_stack.remove(&w);
            scc.insert(w.clone());
            if w == *v {
                break;
            }
        }
        state.sccs.push(scc);
    }
}
