//! Collection and registration-focused verification bridge tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::context_management::with_clean_thread_locals;
use crate::encoder::tests::{expect_error_containing, expect_unknown_containing, expect_verified};
use crate::vc::ObligationKind;
use crate::verify_macro::{self, collect_obligation};
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn test_registration_flow() {
    with_cleared_registrations(|| {
        // Simulate proc macro registering obligations
        register_proof(
            "my_proof",
            vec![
                ProofObligation::assert("check1", "1 + 1 == 2"),
                ProofObligation::assert("check2", "2 * 2 == 4"),
            ],
        );

        // Collect and verify
        let pipeline = VerificationPipeline::collect_from_macros();
        assert_eq!(pipeline.context().obligations().len(), 2);

        let result = pipeline.verify();
        expect_verified(&result, "");
    });
}

#[test]
fn test_clear_registrations_actually_clears() {
    with_cleared_registrations(|| {
        // Register some proofs
        register_proof("proof_a", vec![ProofObligation::assert("check_a", "true")]);
        register_proof(
            "proof_b",
            vec![ProofObligation::assert("check_b", "1 == 1")],
        );

        // Verify registrations exist
        let pipeline = VerificationPipeline::collect_from_macros();
        assert_eq!(
            pipeline.context().obligations().len(),
            2,
            "Should have 2 obligations before clearing"
        );

        // Clear and verify empty
        clear_registrations();
        let pipeline_after = VerificationPipeline::collect_from_macros();
        assert_eq!(
            pipeline_after.context().obligations().len(),
            0,
            "clear_registrations() must remove all registered proofs"
        );
    });
}

#[test]
fn test_clear_registrations_idempotent() {
    with_cleared_registrations(|| {
        clear_registrations(); // double clear shouldn't panic

        let pipeline = VerificationPipeline::collect_from_macros();
        assert_eq!(
            pipeline.context().obligations().len(),
            0,
            "Double clear should leave empty state"
        );
    });
}

#[test]
fn test_collect_from_macros_applies_registered_trait_metadata() {
    with_clean_thread_locals(|| {
        let temp_root = std::env::temp_dir().join(format!(
            "trust-vc-trait-bridge-{}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system clock should be after UNIX_EPOCH")
                .as_nanos()
        ));
        let src_dir = temp_root.join("src");
        fs::create_dir_all(&src_dir).expect("temp src dir should be creatable");
        fs::write(
            temp_root.join("Cargo.toml"),
            "[package]\nname = \"trait_bridge\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .expect("temp Cargo.toml should be writable");
        fs::write(
            src_dir.join("lib.rs"),
            r#"
            #[trust_vc::trait_spec]
            trait CounterSpec {
                #[trust_vc::ensures(result)]
                fn grant(&self, token: bool) -> bool;
            }

            struct Counter;

            #[trust_vc::trait_impl]
            impl CounterSpec for Counter {
                fn grant(&self, token: bool) -> bool {
                    token
                }
            }
            "#,
        )
        .expect("temp trait source should be writable");

        crate::register_traits_from_manifest_scope(
            "src/lib.rs",
            temp_root.to_string_lossy().as_ref(),
        )
        .expect("manifest-scope trait registration should succeed");

        let pipeline = VerificationPipeline::collect_from_macros();
        assert_eq!(pipeline.context().trait_decls().len(), 1);
        assert_eq!(pipeline.context().trait_impl_decls().len(), 1);
        assert_eq!(pipeline.context().trait_decls()[0].name, "CounterSpec");
        assert_eq!(
            pipeline.context().trait_impl_decls()[0].trait_name,
            "CounterSpec"
        );

        let _ = fs::remove_dir_all(&temp_root);
    });
}

#[test]
fn test_collect_from_macros_reports_borrowed_context() {
    with_clean_thread_locals(|| {
        collect_obligation(
            ObligationKind::Assert,
            "borrowed_ctx".to_string(),
            "true".to_string(),
            None,
        );

        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            let result = VerificationPipeline::collect_from_macros().verify();
            expect_error_containing(
                &result,
                "verification context is already borrowed",
                "borrowed proof session",
            );
        });
    });
}

#[test]
fn test_collect_from_macros_reports_borrowed_registered_proofs() {
    with_clean_thread_locals(|| {
        with_registered_proofs_borrowed(|| {
            let result = VerificationPipeline::collect_from_macros().verify();
            expect_error_containing(
                &result,
                "registered proofs are already borrowed",
                "borrowed REGISTERED_PROOFS",
            );
        });
    });
}

#[test]
fn test_collect_from_macros_reports_registered_collection_error() {
    with_clean_thread_locals(|| {
        register_collection_error(TrustVcError::Internal {
            context: "named group manifest",
            detail: "duplicate named reveal group `dup_bundle`".to_string(),
        });

        let pipeline = VerificationPipeline::collect_from_macros();
        match pipeline.collection_error.as_ref() {
            Some(TrustVcError::Internal { context, detail }) => {
                assert_eq!(context, &"named group manifest");
                assert!(
                    detail.contains("dup_bundle"),
                    "registered collection error should preserve manifest detail, got: {detail}"
                );
            }
            other => panic!(
                "registered collection errors should survive collect_from_macros, got: {:?}",
                other
            ),
        }

        let result = pipeline.verify();
        expect_error_containing(
            &result,
            "duplicate named reveal group `dup_bundle`",
            "registered collection errors through verify()",
        );

        clear_registrations();
        let pipeline_after_clear = VerificationPipeline::collect_from_macros();
        assert!(
            pipeline_after_clear.collection_error.is_none(),
            "clear_registrations() must clear queued collection errors"
        );
    });
}

#[test]
fn test_collect_from_macros_keeps_typed_collection_error() {
    with_clean_thread_locals(|| {
        with_registered_proofs_borrowed(|| {
            let pipeline = VerificationPipeline::collect_from_macros();
            match pipeline.collection_error.as_ref() {
                Some(TrustVcError::Internal { context, detail }) => {
                    assert_eq!(context, &"verification bridge collection");
                    assert!(
                        detail.contains("registered proofs are already borrowed"),
                        "typed bridge error should retain the legacy detail text, got: {detail}"
                    );
                }
                other => panic!(
                    "collection failures should now stay on TrustVcError internally, got: {:?}",
                    other
                ),
            }
        });
    });
}

#[test]
fn test_verify_demotes_when_obligation_collection_drops_on_borrow_conflict() {
    with_clean_thread_locals(|| {
        collect_obligation(
            ObligationKind::Assert,
            "kept".to_string(),
            "true".to_string(),
            None,
        );
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            collect_obligation(
                ObligationKind::Assert,
                "dropped".to_string(),
                "true".to_string(),
                None,
            );
        });

        let pipeline = VerificationPipeline::collect_from_macros();
        assert_eq!(
            pipeline.context().obligations().len(),
            1,
            "the kept obligation should still be present after the borrow conflict"
        );

        let result = pipeline.verify();
        expect_unknown_containing(
            &result,
            "silently dropped due to borrow conflict",
            "borrow-conflict drops must fail closed",
        );
        expect_unknown_containing(&result, "#2360", "borrow-conflict issue reference");
        assert_eq!(
            crate::obligation_collection::obligations_dropped_count(),
            0,
            "verify() should consume the dropped-obligation counter once it demotes the result"
        );
    });
}

#[test]
fn test_context_guard_restores_outer_dropped_obligation_count() {
    with_clean_thread_locals(|| {
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            collect_obligation(
                ObligationKind::Assert,
                "outer_dropped".to_string(),
                "true".to_string(),
                None,
            );
        });
        assert_eq!(crate::obligation_collection::obligations_dropped_count(), 1);

        let guard = verify_macro::save_context_guard();
        assert_eq!(
            crate::obligation_collection::obligations_dropped_count(),
            0,
            "nested proof scopes should start with a fresh dropped-obligation counter"
        );
        crate::proof_session::with_session_cell(|cell| {
            let _borrow = cell.borrow_mut();
            collect_obligation(
                ObligationKind::Assert,
                "inner_dropped".to_string(),
                "true".to_string(),
                None,
            );
        });
        assert_eq!(crate::obligation_collection::obligations_dropped_count(), 1);

        guard.restore();
        assert_eq!(
            crate::obligation_collection::obligations_dropped_count(),
            1,
            "restoring the outer context must restore its prior dropped-obligation count"
        );
    });
}
