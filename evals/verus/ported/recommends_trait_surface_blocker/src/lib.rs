// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(dead_code, unexpected_cfgs)]

use trust_vc_types::Seq;

type Int = i32;

fn forall<T, F>(_f: F) -> bool
where
    F: Fn(T) -> bool,
{
    true
}

struct RecommendsImplementor<T> {
    t: T,
}

trait RecommendsTr<Key> {
    fn trait_fn(s: Seq<u8>) -> Option<Key>;
}

impl<S> RecommendsTr<S> for RecommendsImplementor<S> {
    fn trait_fn(_s: Seq<u8>) -> Option<S> {
        None
    }
}

// Current-syntax regression fixture for the upstream issue1566 shape: a
// quantified postcondition calls an associated trait spec function and then
// depends on an impossible recommends side condition. The full upstream case
// still needs trigger, existential, uninterpreted spec-function, and callee
// recommends propagation parity; this fixture keeps the qualified associated
// trait function surface compile-checked.
#[trust_vc::contract(
    ensures(forall(|s: Seq<u8>| {
        match <RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s) {
            Some(_x) => forall(|witness: Int| false || witness != witness),
            None => false,
        }
    })),
    returns(result)
)]
fn recommends_trait_associated_spec_surface_blocker() {}

#[trust_vc::contract(
    recommends(forall(|s: Seq<u8>| {
        match <RecommendsImplementor<u8> as RecommendsTr<u8>>::trait_fn(s) {
            Some(_x) => forall(|witness: Int| false || witness != witness),
            None => false,
        }
    })),
    ensures(true),
    returns(result)
)]
fn recommends_quantified_associated_spec_surface_regression() {}
