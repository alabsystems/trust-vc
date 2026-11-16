// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compiler tracking deliberately omits these invocation dimensions. The
//! native owner still rejects a client that changes them from its producer.

use super::*;

fn rejects_untracked_change(name: &str, mutate: impl FnOnce(&mut Options)) {
    let producer = Options::default();
    let mut client = producer.clone();
    mutate(&mut client);
    assert_eq!(
        producer.dep_tracking_hash(false),
        client.dep_tracking_hash(false)
    );
    let refusal = check(&producer, &client).unwrap_err();
    assert!(refusal.contains(name), "{name}: {refusal}");
}

#[test]
fn the_same_current_compiler_options_retain_their_native_baseline() {
    let producer = Options::default();
    assert!(check(&producer, &producer.clone()).is_ok());
}

#[test]
fn native_worker_selectors_cannot_hide_behind_the_tracking_hash() {
    rejects_untracked_change("resource_worker_v2", |opts| opts.resource_worker_v2 = true);
    rejects_untracked_change("resource_worker_v3", |opts| opts.resource_worker_v3 = true);
    rejects_untracked_change("resource_subgroups_v3", |opts| {
        opts.resource_subgroups_v3 = true
    });
}

#[test]
fn admission_and_object_retention_options_require_the_producer_baseline() {
    rejects_untracked_change("trust_drop_rlib_objects", |opts| {
        opts.unstable_opts.trust_drop_rlib_objects = true;
    });
    rejects_untracked_change("trust_admission_run_digest", |opts| {
        opts.unstable_opts.trust_admission_run_digest = Some("changed".into());
    });
    rejects_untracked_change("trust_admission_unit_digest", |opts| {
        opts.unstable_opts.trust_admission_unit_digest = Some("changed".into());
    });
    rejects_untracked_change("trust_admission_semantics_digest", |opts| {
        opts.unstable_opts.trust_admission_semantics_digest = Some("changed".into());
    });
    rejects_untracked_change("trust_admission_unit_role", |opts| {
        opts.unstable_opts.trust_admission_unit_role = Some("changed".into());
    });
    rejects_untracked_change("trust_admission_compile_target", |opts| {
        opts.unstable_opts.trust_admission_compile_target = Some("changed".into());
    });
}
