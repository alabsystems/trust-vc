//! Restrict transitive macro lookup to the owned copied dependency view.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeSet;
use std::path::PathBuf;

/// Select lookup paths without changing explicit extern operands. The
/// original builtin stays pinned while its transitive lookup uses the checked
/// nonmacro links beside the copied macro images.
pub(super) fn selected_directories(
    mut directories: BTreeSet<PathBuf>,
    original: &BTreeSet<PathBuf>,
    selected: &BTreeSet<PathBuf>,
) -> Result<BTreeSet<PathBuf>, String> {
    if original.is_empty() || selected.len() != 1 {
        return Err("the closed client needs one selected macro dependency directory".into());
    }
    if original != selected && selected.iter().any(|path| original.contains(path)) {
        return Err("the copied macro dependency view overlaps an original directory".into());
    }
    for path in original {
        if !directories.remove(path) {
            return Err("the original macro dependency directory inventory changed".into());
        }
    }
    directories.extend(selected.iter().cloned());
    Ok(directories)
}

pub(super) fn selected_search(
    args: Vec<String>,
    original: &BTreeSet<PathBuf>,
    selected: &BTreeSet<PathBuf>,
) -> Result<Vec<String>, String> {
    if args.is_empty() {
        return Err("the closed client argv is empty".into());
    }
    let unchanged = original == selected;
    let mut kept = Vec::new();
    let mut directories = BTreeSet::new();
    let mut at = 0;
    while at < args.len() {
        if args[at] == "-L" {
            let value = args
                .get(at + 1)
                .ok_or("incomplete closed dependency search argument")?;
            let path = value
                .strip_prefix("dependency=")
                .ok_or("the closed client only accepts dependency search paths")?;
            let path = PathBuf::from(path);
            directories.insert(path.clone());
            if original.contains(&path) {
                at += 2;
                continue;
            }
            kept.extend([args[at].clone(), value.clone()]);
            at += 2;
        } else {
            if args[at].starts_with("-L") {
                return Err("the closed recipe only accepts paired -L arguments".into());
            }
            kept.push(args[at].clone());
            at += 1;
        }
    }
    selected_directories(directories, original, selected)?;
    if unchanged {
        return Ok(args);
    }
    let insert = kept.iter().position(|arg| arg == "-L").unwrap_or(1);
    let selected = selected
        .iter()
        .next()
        .ok_or("the closed client has no selected macro dependency directory")?;
    kept.splice(
        insert..insert,
        ["-L".into(), format!("dependency={}", selected.display())],
    );
    Ok(kept)
}

#[cfg(test)]
mod tests;
