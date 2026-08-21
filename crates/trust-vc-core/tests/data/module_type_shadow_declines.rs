// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! DECLINE PINS: the colliding-bare-name shapes scope-relative resolution
//! deliberately refuses to settle. Each one is information this per-file, syn
//! -level walk genuinely does not have; guessing at any of them would reopen the
//! FV-1 cardinal false-verify from the other side.

// ---- glob import: the glob's contents are not knowable from this file ----

mod glob_a {
    pub struct G {
        pub v: u8,
    }
}

mod glob_b {
    pub struct G {
        pub v: u64,
    }
}

use glob_a::*;

/// DECLINE: a glob binds whatever its target module exports, including that
/// module's own re-exports, so `G` here cannot be attributed to either
/// declaration. (`use super::*`, which only re-imports an ancestor scope the
/// walk already visits, is NOT this case.)
#[trust_vc::ensures(true)]
fn glob_import_declines(g: G) -> u64 {
    trust_vc::assert!(g.v <= 255u8);
    0u64
}

// ---- cfg-gated arms: no cfg is evaluated, so both arms are live ----

#[cfg(feature = "wide")]
pub struct C {
    pub v: u64,
}

#[cfg(not(feature = "wide"))]
pub struct C {
    pub v: u8,
}

/// DECLINE: the two arms are declared in the SAME module and differ, and this
/// walk does not evaluate `cfg`. Scope cannot tell them apart, so neither is
/// adopted.
#[trust_vc::ensures(true)]
fn cfg_gated_declaration_declines(c: C) -> u64 {
    trust_vc::assert!(c.v <= 255u8);
    0u64
}

// ---- import from another file/crate that shadows an in-file leaf ----

mod local_x {
    pub struct E {
        pub v: u8,
    }
}

mod local_y {
    pub struct E {
        pub v: u64,
    }
}

use elsewhere::E;

/// DECLINE: `E` is bound by an import whose target module is not declared in
/// this file, so the use site names a type that is out of reach entirely.
/// Falling through to either in-file `E` would answer with a type the use site
/// does not name — the failure mode is a wrong answer, not a missing one.
#[trust_vc::ensures(true)]
fn out_of_file_import_declines(e: E) -> u64 {
    trust_vc::assert!(e.v <= 255u8);
    0u64
}

// ---- renamed import: introduces a name no declaration carries ----

mod ren_a {
    pub struct W {
        pub v: u8,
    }
}

mod ren_b {
    pub struct W {
        pub v: u64,
    }
}

use ren_a::W as Wide;

/// DECLINE: `Wide` names no declaration, and mapping an introduced name onto a
/// declaration is the general in-scope-name resolver this change deliberately
/// does not build. Scope-relative arbitration only ever CHOOSES among
/// declarations that already share a bare name.
#[trust_vc::ensures(true)]
fn renamed_import_declines(w: Wide) -> u64 {
    trust_vc::assert!(w.v <= 255u8);
    0u64
}
