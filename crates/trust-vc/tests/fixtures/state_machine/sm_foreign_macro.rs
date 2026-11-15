// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A THIRD-PARTY item macro whose last path segment happens to be
//! `state_machine`.
//!
//! D1a keys admission on the last path segment (`expand::MACRO_NAMES`), so an
//! unrelated DSL spelled `<crate>::state_machine!` is neither expanded nor
//! ignored: it is POISONED, and the file reports a refusal at the invocation
//! line. That is deliberate and fail-closed — trust-vc cannot know what such a
//! macro expands to, and silently ignoring it is exactly the HEAD hole D1a
//! closes for a Verus-style machine.
//!
//! The foreign macro is also a macro whose expansion trust-vc does not read:
//! it can emit an impl, a trait or a type that changes what any function of the
//! file does. So the unread-item rule refuses a `Verified` answer for every
//! function of the file, and a refutation is kept:
//!
//! | case | verdict |
//! |---|---|
//! | `foreign_untouched_control` | `Error` (unread item) |
//! | `foreign_untouched_liar` | `Counterexample` |
//! | `foreign_machine_client` | `Error` + pinned reason |

#![allow(dead_code, unused_variables)]

use trust_vc_types::int;

// The macro is never expanded, so its body is arbitrary tokens.
other_dsl::state_machine! { Widget { anything at all } }

/// TRUE, but in a file whose foreign macro is not read: refused.
#[trust_vc::proof]
#[trust_vc::requires(a >= 0 && b >= 0)]
#[trust_vc::ensures(a + b >= a)]
fn foreign_untouched_control(a: int, b: int) {}

/// The other half of the discriminator: a poisoned file must still REFUTE.
#[trust_vc::proof]
#[trust_vc::requires(a >= 0 && b >= 0)]
#[trust_vc::ensures(a + b > a)]
fn foreign_untouched_liar(a: int, b: int) {}

/// A function that REFERENCES the refused machine fails closed.
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn foreign_machine_client(s: Widget::State) {}
