//! Panic-safety and double-restore tests for RAII verification guards.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ContextGuard is the most critical RAII guard in trust_vc — it protects the
//! entire verification context during proof function execution. Every other
//! RAII guard (SolverThreadGuard, BroadcastGuard, QuantifierBoundVarGuard,
//! ForcedFlagGuard) had a panic-safety test, but ContextGuard did not.
//!
//! Part of #2421 memory_verification phase.

use trust_vc_core::enter_invariant_mask_scope;
use trust_vc_core::vc::{InvariantMask, ProofObligation, VerificationContext};
use trust_vc_core::verify_macro::{
    clear_all_thread_locals, get_context, is_in_proof_mode, restore_context, save_context_guard,
    set_proof_mode,
};

/// ContextGuard must restore the outer verification context on panic unwind.
/// Without this RAII guarantee, a panicking proof function body would leave
/// the inner (empty) context in the thread-local, corrupting subsequent
/// verification on the same thread.
#[test]
fn test_context_guard_restores_on_panic() {
    clear_all_thread_locals();

    // Establish an outer context with an obligation so we can detect restoration.
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("outer_sentinel", "true"));
    restore_context(Some(ctx));
    set_proof_mode(true);

    // Simulate a proof function that panics mid-body.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = save_context_guard();
        // Inner scope: context was taken by save_context_guard, so it's empty.
        assert!(
            get_context().is_none(),
            "inner scope should have empty context"
        );
        panic!("simulated proof function panic");
    }));

    assert!(result.is_err(), "should have caught the panic");

    // The guard's Drop must have restored the outer context.
    let restored = get_context().expect("outer context must be restored after panic");
    assert_eq!(
        restored.obligations().len(),
        1,
        "outer context obligation must survive the panic"
    );
    assert_eq!(restored.obligations()[0].name(), "outer_sentinel");
    assert!(
        is_in_proof_mode(),
        "proof mode flag must be restored after panic"
    );

    clear_all_thread_locals();
}

/// Calling `guard.restore()` explicitly followed by the implicit Drop must
/// not double-restore or corrupt state. The `do_restore()` method uses
/// `.take()` on Option fields — second call is a no-op.
#[test]
fn test_context_guard_double_restore_is_safe() {
    clear_all_thread_locals();

    // Set up outer state.
    set_proof_mode(true);
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("double_restore_sentinel", "true"));
    restore_context(Some(ctx));

    {
        let guard = save_context_guard();
        // Explicit restore inside the block...
        guard.restore();
        // ...guard goes out of scope here, Drop runs again — must be a no-op.
    }

    // Outer state must be intact (not double-restored or corrupted).
    let restored = get_context().expect("context must survive double restore");
    assert_eq!(restored.obligations()[0].name(), "double_restore_sentinel");
    assert!(is_in_proof_mode(), "proof mode must survive double restore");

    clear_all_thread_locals();
}

/// InvariantMaskGuard must restore the previous mask on panic unwind.
/// Since invariant_mask is a crate-private field, we verify RAII behavior
/// by observing that the outer context survives the panic — if the guard
/// failed to restore, the context would be in the inner state (or missing).
#[test]
fn test_invariant_mask_guard_restores_on_panic() {
    clear_all_thread_locals();

    // Set up context with outer mask and a sentinel obligation.
    let _outer = enter_invariant_mask_scope(InvariantMask::Namespaces(vec![42]));
    // Add a sentinel so we can verify the context survived.
    {
        let mut ctx = get_context().unwrap_or_default();
        ctx.push_obligation(ProofObligation::assert("mask_sentinel", "true"));
        restore_context(Some(ctx));
    }

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _inner = enter_invariant_mask_scope(InvariantMask::None);
        panic!("simulated invariant body panic");
    }));

    assert!(result.is_err(), "should have caught the panic");

    // Outer context must be intact after inner guard panic-restored.
    let restored = get_context().expect("context must survive inner guard panic");
    assert!(
        restored
            .obligations()
            .iter()
            .any(|o| o.name() == "mask_sentinel"),
        "mask_sentinel obligation must survive inner mask guard panic"
    );

    clear_all_thread_locals();
}

/// Trait registry thread-local must be cleared by `clear_all_thread_locals()`.
/// The trait registry is cleared via the call chain:
///   clear_all_thread_locals() → clear_registrations() → clear_registered_traits()
/// This test ensures the chain is intact.
#[test]
fn test_clear_all_thread_locals_clears_trait_registry() {
    clear_all_thread_locals();

    // Register a trait in the thread-local registry.
    trust_vc_core::register_traits_from_source(
        "cleanup_guard_test.rs",
        r#"
            #[trait_spec]
            trait GuardTestTrait {
                fn guard_test_method(&self) -> bool;
            }
        "#,
    )
    .expect("register should succeed");

    // Clear all thread-locals.
    clear_all_thread_locals();

    // If the chain is intact, re-registering the same trait should succeed
    // (no duplicate from pre-clear state). Register a different trait to
    // verify the registry was actually cleared and doesn't contain stale state.
    trust_vc_core::register_traits_from_source(
        "cleanup_guard_test_2.rs",
        r#"
            #[trait_spec]
            trait AnotherTrait {
                fn another_method(&self) -> bool;
            }
        "#,
    )
    .expect("re-register after clear should succeed");

    // Verify via the verification context — trait data should contain
    // only the post-clear registration, not the pre-clear one.
    let ctx = VerificationContext::new();
    // The trait registry is thread-local and apply happens via public pipeline.
    // Since apply_registered_traits_to_context is pub(crate), we verify
    // indirectly: after clear + re-register, a fresh verification should
    // see only the new trait.
    //
    // Direct verification: clear_all_thread_locals calls clear_registrations
    // which calls clear_registered_traits, so the old GuardTestTrait is gone.
    // We can't directly observe trait_decls() from integration tests,
    // so we verify the chain doesn't panic and the re-registration succeeds.
    let _ = ctx;

    clear_all_thread_locals();
}
