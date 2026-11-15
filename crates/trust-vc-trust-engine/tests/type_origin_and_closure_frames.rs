// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Wire v58: the nominal type-origin key (`StructDef.origin`, `EnumDef.origin`)
//! and declared closure frames (`Module.closure_layouts`).
//!
//! Neither lane models a nominal type or a closure: the native lane has no sort
//! for `Ty::Struct`, `Ty::Enum` or `Ty::Closure` and declines a closure
//! application, and the body lane refuses all of them. What the crate owes v58
//! is at its module boundaries: the native input gate refuses a key claimed
//! twice and an incoherent frame by name, and the body lane's semantic digest
//! moves with both tables.

#[path = "support/admission_baseline.rs"]
mod admission_baseline;
#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use trust_ir::request::NativeVerificationBundle;
use trust_ir::ty::{FieldDef, StructDef, StructRepr, Ty, TypeOrigin};
use trust_ir::{ClosureLayoutDescriptor, ClosureTy, FuncTyId, Module, ProofDigest, StructId};
use trust_vc_trust_engine::{
    trust_ir_body_semantic_digest, TrustEngineError, TrustVcNativeTrustIrBundleReport,
    TrustVcNativeTrustIrDischargeStatus, TrustVcTrustEngine,
};

const DISCHARGE_SCALAR_BRANCH: &str =
    include_str!("../fixtures/trust_ir_native/discharge_scalar_branch.json");
const CLAMP_POST: &str = "vc:clamp:postcondition:0";

fn rust_key(path: u8) -> TypeOrigin {
    TypeOrigin::Rust {
        stable_crate_id: 0x7c0f_fee0_0000_0001,
        def_path_hash: [path; 16],
        args_digest: ProofDigest::sha256([0; 32]),
    }
}

/// `struct <name> { v: <ty> }`, keyed by `origin` when one is given.
fn one_field_struct(name: &str, ty: Ty, origin: Option<TypeOrigin>) -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: name.to_string(),
        fields: vec![FieldDef {
            name: "v".to_string(),
            ty,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin,
    }
}

/// A closure over the module's first signature capturing one `u32`, with the
/// declared frame `(size, align, capture offset)` when one is given.
fn add_u32_closure(module: &mut Module, frame: Option<(u64, u64, u64)>) {
    let closure = module
        .add_closure_type(ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::U32],
        })
        .expect("Module::add_closure_type: test fixture");
    if let Some((size, align, offset)) = frame {
        module.closure_layouts.push(ClosureLayoutDescriptor {
            closure,
            size,
            align,
            capture_offsets: vec![offset],
            origin: None,
        });
    }
}

/// The clamp discharge fixture with `edit` applied to its module, every
/// identity resealed, consumed through the native lane.
fn consume_clamp(
    edit: impl FnOnce(&mut Module),
) -> Result<TrustVcNativeTrustIrBundleReport, TrustEngineError> {
    let mut bundle: NativeVerificationBundle =
        serde_json::from_str(DISCHARGE_SCALAR_BRANCH).expect("discharge fixture should decode");
    edit(&mut bundle.module);
    admission_baseline::reseal_module_identity(&mut bundle);
    TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle)
}

fn clamp_post(report: &TrustVcNativeTrustIrBundleReport) -> &TrustVcNativeTrustIrDischargeStatus {
    report.requests()[0]
        .discharge()
        .iter()
        .find(|outcome| outcome.public_obligation_id() == Some(CLAMP_POST))
        .expect("clamp's postcondition is reported")
        .outcome()
}

fn producer_refusal(result: Result<TrustVcNativeTrustIrBundleReport, TrustEngineError>) -> String {
    match result {
        Err(TrustEngineError::NativeTrustIrModuleRejectedByProducerValidator {
            errors, ..
        }) => errors,
        other => panic!("expected the producer validator's refusal, got {other:?}"),
    }
}

#[test]
fn a_type_origin_claimed_twice_is_refused_and_two_keys_are_two_types() {
    let control = consume_clamp(|_| {}).expect("the clamp fixture is a valid bundle");
    assert_eq!(
        clamp_post(&control),
        &TrustVcNativeTrustIrDischargeStatus::Verified,
        "the control must verify, or the probe below proves nothing"
    );

    // Two definitions under two keys are two types, and a table entry the
    // body never names changes no verdict.
    let two_keys = consume_clamp(|module| {
        module
            .add_struct_def(one_field_struct("Wide", Ty::U64, Some(rust_key(1))))
            .expect("fixture struct ID space is available");
        module
            .add_struct_def(one_field_struct("Narrow", Ty::U32, Some(rust_key(2))))
            .expect("fixture struct ID space is available");
    })
    .expect("two keys are two types");
    assert_eq!(
        clamp_post(&two_keys),
        &TrustVcNativeTrustIrDischargeStatus::Verified
    );

    // The same two definitions under ONE key: one source entity with two
    // images, which no consumer can resolve.
    let errors = producer_refusal(consume_clamp(|module| {
        module
            .add_struct_def(one_field_struct("Wide", Ty::U64, Some(rust_key(1))))
            .expect("fixture struct ID space is available");
        module
            .add_struct_def(one_field_struct("Narrow", Ty::U32, Some(rust_key(1))))
            .expect("fixture struct ID space is available");
    }));
    assert!(
        errors.contains("is claimed twice in one module")
            && errors.contains("`Wide`")
            && errors.contains("`Narrow`"),
        "the refusal must name the key's two claimants: {errors}"
    );
}

#[test]
fn an_incoherent_closure_frame_is_refused_and_its_coherent_twin_is_not() {
    let framed = consume_clamp(|module| add_u32_closure(module, Some((4, 4, 0))))
        .expect("a coherent closure frame is a valid module");
    assert_eq!(
        clamp_post(&framed),
        &TrustVcNativeTrustIrDischargeStatus::Verified
    );

    // The same frame with its one capture placed past the frame's end.
    let errors = producer_refusal(consume_clamp(|module| {
        add_u32_closure(module, Some((4, 4, 4)));
    }));
    assert!(
        errors.contains("declared closure layout table: Module.closure_layouts: "),
        "the refusal must name the closure layout table: {errors}"
    );
}

#[test]
fn the_semantic_digest_moves_with_type_origin_keys_and_closure_frames() {
    let fixture = fixtures::guarded_checked_add_u8();
    let digest = |module: &Module| {
        trust_ir_body_semantic_digest(module, fixture.function())
            .expect("a v58 module has a wire identity")
    };
    let edited = |edit: &dyn Fn(&mut Module)| {
        let mut module = fixture.module.clone();
        edit(&mut module);
        digest(&module)
    };
    let variants = [
        ("the fixture", digest(&fixture.module)),
        (
            "an unkeyed struct",
            edited(&|module| {
                module
                    .add_struct_def(one_field_struct("Wide", Ty::U64, None))
                    .expect("fixture struct ID space is available");
            }),
        ),
        (
            "the struct under a Rust key",
            edited(&|module| {
                module
                    .add_struct_def(one_field_struct("Wide", Ty::U64, Some(rust_key(1))))
                    .expect("fixture struct ID space is available");
            }),
        ),
        (
            "the struct under another Rust key",
            edited(&|module| {
                module
                    .add_struct_def(one_field_struct("Wide", Ty::U64, Some(rust_key(2))))
                    .expect("fixture struct ID space is available");
            }),
        ),
        (
            "the struct under a Clean key",
            edited(&|module| {
                module
                    .add_struct_def(one_field_struct(
                        "Wide",
                        Ty::U64,
                        Some(TypeOrigin::Clean {
                            decl: "Trust.Wide".to_string(),
                            env_digest: ProofDigest::sha256([3; 32]),
                        }),
                    ))
                    .expect("fixture struct ID space is available");
            }),
        ),
        (
            "a closure with no frame",
            edited(&|module| add_u32_closure(module, None)),
        ),
        (
            "the closure with a declared frame",
            edited(&|module| add_u32_closure(module, Some((4, 4, 0)))),
        ),
        (
            "the closure with a wider frame",
            edited(&|module| add_u32_closure(module, Some((8, 4, 4)))),
        ),
    ];
    for (index, (label, value)) in variants.iter().enumerate() {
        for (other, other_value) in &variants[..index] {
            assert_ne!(value, other_value, "{label} and {other} share a digest");
        }
    }
    assert_eq!(
        variants[2].1,
        edited(&|module| {
            module
                .add_struct_def(one_field_struct("Wide", Ty::U64, Some(rust_key(1))))
                .expect("fixture struct ID space is available");
        }),
        "the digest is a function of the module"
    );
}
