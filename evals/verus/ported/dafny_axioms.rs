// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_types::Set;

#[trust_vc::requires(s.contains(a))]
#[trust_vc::ensures(s.insert(a).len() == s.len())]
fn set_axiom_01<T: Copy>(s: Set<T>, a: T) {}

#[trust_vc::requires(!s.contains(a) && s.len() < usize::MAX)]
#[trust_vc::ensures(s.insert(a).len() == s.len() + 1usize)]
fn set_axiom_02<T: Copy>(s: Set<T>, a: T) {}

#[trust_vc::requires(s.contains(a) && s.len() > 0usize)]
#[trust_vc::ensures(s.remove(a).len() == s.len() - 1usize)]
fn set_axiom_03_present<T: Copy>(s: Set<T>, a: T) {}

#[trust_vc::requires(!s.contains(a))]
#[trust_vc::ensures(s.remove(a).len() == s.len())]
fn set_axiom_03_absent<T: Copy>(s: Set<T>, a: T) {}
