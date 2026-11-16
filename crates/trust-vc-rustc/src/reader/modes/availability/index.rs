//! Side indexes preserve the ordered physical fact roster.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;
use std::hash::Hash;

pub(super) fn get<'a, K: Eq + Hash, T>(
    rows: &'a [T],
    positions: &HashMap<K, usize>,
    key: &K,
    key_of: impl Fn(&T) -> K,
) -> Result<Option<&'a T>, String> {
    let Some(position) = positions.get(key) else {
        return Ok(None);
    };
    let row = rows
        .get(*position)
        .ok_or("an availability index is outside its physical fact roster")?;
    if key_of(row) != *key {
        return Err("an availability index names another physical occurrence".into());
    }
    Ok(Some(row))
}

pub(super) fn insert<K: Eq + Hash, T: PartialEq>(
    rows: &mut Vec<T>,
    positions: &mut HashMap<K, usize>,
    key: K,
    fact: T,
    key_of: impl Fn(&T) -> K,
    contradiction: &'static str,
) -> Result<(), String> {
    if positions.len() != rows.len() {
        return Err("an availability index lost its physical fact roster".into());
    }
    if key_of(&fact) != key {
        return Err("an availability insertion names another occurrence".into());
    }
    if let Some(previous) = get(rows, positions, &key, key_of)? {
        if previous != &fact {
            return Err(contradiction.into());
        }
    } else {
        let position = rows.len();
        rows.push(fact);
        positions.insert(key, position);
    }
    Ok(())
}

pub(super) fn validate<K: Eq + Hash, T>(
    rows: &[T],
    positions: &HashMap<K, usize>,
    key_of: impl Fn(&T) -> K,
) -> Result<(), String> {
    if positions.len() != rows.len() {
        return Err("an availability index has a different physical occurrence count".into());
    }
    for (position, row) in rows.iter().enumerate() {
        if positions.get(&key_of(row)) != Some(&position) {
            return Err("an availability index changed physical occurrence order".into());
        }
    }
    Ok(())
}
