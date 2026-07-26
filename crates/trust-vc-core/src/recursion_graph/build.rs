//! Call-graph assembly over the shared source-tree walker.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};
use std::path::Path;

use syn::visit::Visit;

use crate::mode_attrs;
use crate::mode_index::{CanonicalFnPath, CrateModeIndex};
use crate::mode_paths::{self, PathCallCollector};
use crate::source_tree;

use super::CrateCallGraph;

/// Builds a call graph by walking the crate source tree.
pub(super) fn build_call_graph(
    crate_root: &Path,
    index: &CrateModeIndex,
) -> Option<CrateCallGraph> {
    let mut edges: HashMap<CanonicalFnPath, HashSet<CanonicalFnPath>> = HashMap::new();

    source_tree::walk_crate_modules(crate_root, &mut |m| {
        for item in m.items {
            match item {
                syn::Item::Fn(item_fn) => {
                    let fn_name = item_fn.sig.ident.to_string();
                    let mut path_segs = m.module_path.to_vec();
                    path_segs.push(fn_name);
                    let caller = CanonicalFnPath(path_segs);

                    let callees = collect_callees(&item_fn.block, m.module_path, index);
                    edges.insert(caller, callees);
                }
                // Collect call edges from methods inside impl blocks.
                // Mirrors the index scanning in mode_index. Fix for #2550 F1.
                syn::Item::Impl(item_impl) => {
                    if let Some(type_name) = mode_attrs::extract_impl_type_name(&item_impl.self_ty)
                    {
                        let mut impl_path = m.module_path.to_vec();
                        impl_path.push(type_name);
                        for impl_item in &item_impl.items {
                            if let syn::ImplItem::Fn(method) = impl_item {
                                let method_name = method.sig.ident.to_string();
                                let mut path_segs = impl_path.clone();
                                path_segs.push(method_name);
                                let caller = CanonicalFnPath(path_segs);

                                let callees = collect_callees(&method.block, m.module_path, index);
                                edges.insert(caller, callees);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    })?;

    Some(CrateCallGraph { edges })
}

/// Collects resolved callees from a function/method body.
fn collect_callees(
    block: &syn::Block,
    module_path: &[String],
    index: &CrateModeIndex,
) -> HashSet<CanonicalFnPath> {
    let mut collector = PathCallCollector::default();
    collector.visit_block(block);

    let mut callees = HashSet::new();
    for call in &collector.calls {
        if let Some(resolved) = mode_paths::resolve_call_path(call, module_path, index) {
            callees.insert(resolved);
        }
    }
    callees
}
