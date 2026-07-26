//! Broadcast assumption tests — bound_vars, trigger patterns, and instance cap.
//!
//! Issues: #1613, #1629, #1866, #2113, #2414, #2461, #2575
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

mod activation;
mod cap_context;
mod guards;
mod multi_var;
mod triggers;

fn ground_broadcast(name: &str, condition: &str) -> crate::vc::ProofObligation {
    crate::vc::ProofObligation::broadcast_assume(name, condition).with_bound_vars(vec![])
}

fn grouped_ground_broadcast(
    name: &str,
    condition: &str,
    group: &str,
) -> crate::vc::ProofObligation {
    ground_broadcast(name, condition).with_broadcast_group(group)
}
