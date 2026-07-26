//! Direct cleanup regressions for thread-local trait metadata.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2421 memory_verification phase.

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::{register_traits_from_source, verify_macro::clear_all_thread_locals};

const TRAIT_SOURCE: &str = r#"
    #[trait_spec]
    trait CleanupTrait {
        fn permits(&self, token: bool) -> bool;
    }

    struct CleanupWitness;

    #[trait_impl]
    impl CleanupTrait for CleanupWitness {
        fn permits(&self, token: bool) -> bool {
            token
        }
    }
"#;

#[test]
fn test_clear_all_thread_locals_removes_trait_metadata_from_pipeline() {
    common::with_clean_verification(|| {
        register_traits_from_source("cleanup_trait.rs", TRAIT_SOURCE)
            .expect("initial trait registration should succeed");

        let before_clear = VerificationPipeline::collect_from_macros();
        assert_eq!(
            before_clear.context().trait_decls().len(),
            1,
            "pipeline should expose the registered trait declaration before cleanup"
        );
        assert_eq!(
            before_clear.context().trait_impl_decls().len(),
            1,
            "pipeline should expose the registered trait impl before cleanup"
        );
        assert_eq!(before_clear.context().trait_decls()[0].name, "CleanupTrait");
        assert_eq!(
            before_clear.context().trait_impl_decls()[0].trait_name,
            "CleanupTrait"
        );

        clear_all_thread_locals();

        let after_clear = VerificationPipeline::collect_from_macros();
        assert!(
            after_clear.context().trait_decls().is_empty(),
            "clear_all_thread_locals() must remove pre-clear trait declarations"
        );
        assert!(
            after_clear.context().trait_impl_decls().is_empty(),
            "clear_all_thread_locals() must remove pre-clear trait impls"
        );

        register_traits_from_source("cleanup_trait.rs", TRAIT_SOURCE)
            .expect("re-registration after cleanup should succeed");

        let after_reregister = VerificationPipeline::collect_from_macros();
        assert_eq!(
            after_reregister.context().trait_decls().len(),
            1,
            "cleanup should leave the registry empty so the same source can repopulate it"
        );
        assert_eq!(
            after_reregister.context().trait_impl_decls().len(),
            1,
            "cleanup should leave the impl registry empty so the same source can repopulate it"
        );
    });
}
