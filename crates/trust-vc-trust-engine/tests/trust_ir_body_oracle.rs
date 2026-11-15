// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The semantic oracle for the trust-ir body lane.
//!
//! The oracle is trust-ir's OWN reference interpreter (`trust_ir::Interpreter`,
//! `interpret.rs`), which is written independently of this lane's lowering —
//! unlike a local interpreter, which would only agree with the author of the
//! lowering. Every fixture with at most two 8-bit parameters is enumerated
//! EXHAUSTIVELY (all 256 or 65 536 inputs) and the lane's verdict is required
//! to be exactly what the interpreter says:
//!
//! * `DischargedAdvisory` iff no input panics the site and at least one input
//!   reaches it;
//! * `Refuted` / `RefutedIgnoringPriorAsserts` iff some input panics the site,
//!   with the reported witness replaying accordingly;
//! * `NotAnswerable(VacuousPremises)` iff no input reaches the site at all.
//!
//! The variant construction here is a second, independent implementation of
//! the one in `src/trust_ir_body/replay.rs`: if they disagree the oracle
//! fails.
//!
//! # What reading this agreement is about
//!
//! Both implementations instantiate `Inst::Undef` as a concrete constant,
//! because the pinned interpreter refuses to execute an `Undef` at all
//! (`interpret.rs:652`). So for a fixture carrying Trust's checked-op pack the
//! agreement established here is with the HAVOC reading, not with the module
//! as written. That is not left implicit: this file derives, independently of
//! the lane, whether a seed precedes each site, and requires the lane's
//! declared `BodyReading` to match. For every site declared
//! `PinnedInterpreter` it additionally requires the module AS WRITTEN to be
//! executable, so those agreements really are about the pinned semantics.

#[path = "support/trust_ir_body_fixtures.rs"]
mod fixtures;

use std::collections::BTreeSet;

use fixtures::Fixture;
use trust_ir::{
    BlockId, Constant, FuncId, FuncTy, FuncTyId, Inst, InstrNode, InterpretErrorCode,
    InterpretOptions, InterpretValue, Interpreter, Module, ObligationSite, OverflowOp, Ty, ValueId,
};
use trust_vc_trust_engine::{
    BodyReading, TrustIrBodyOptions, TrustIrBodyRefusal, TrustIrBodyVerdict, TrustIrBodyWitness,
    TrustIrScalar, TrustVcTrustEngine,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Variant {
    Site,
    Pre,
    Prior,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    Reached,
    Panic,
    UndefinedBehavior,
    /// A false `Assume`: the input lies outside the assumed domain (trust-ir
    /// `InterpretErrorCode::AssumeViolated`; UB before WS2.11 named it apart).
    AssumeViolated,
    Other(String),
}

/// Chain order, derived here rather than taken from the lane.
fn chain(module: &Module, function: FuncId) -> Vec<BlockId> {
    let target = module.function_by_id(function).expect("function exists");
    let mut order = Vec::new();
    let mut current = target.entry;
    let mut guard = 0;
    loop {
        order.push(current);
        let block = target
            .blocks
            .iter()
            .find(|block| block.id == current)
            .expect("chain block exists");
        match block.body.last().map(|node| &node.inst) {
            Some(Inst::Br { target, .. }) => current = *target,
            _ => break,
        }
        guard += 1;
        assert!(guard < 64, "fixture chain is not acyclic");
    }
    order
}

/// Independent re-implementation of the executable variant.
fn variant_module(
    module: &Module,
    function: FuncId,
    site: ObligationSite,
    variant: Variant,
) -> Module {
    variant_module_inner(module, function, site, variant, true)
}

/// `instantiate_havoc == false` builds the same variant WITHOUT rewriting any
/// `Inst::Undef`, so the two can be compared to prove a variant is a literal
/// sub-program of the module as written.
fn variant_module_inner(
    module: &Module,
    function: FuncId,
    site: ObligationSite,
    variant: Variant,
    instantiate_havoc: bool,
) -> Module {
    variant_module_seeded(module, function, site, variant, instantiate_havoc, false)
}

/// `ones_seed` picks a DIFFERENT havoc instantiation, to prove the choice is
/// unobservable.
fn variant_module_seeded(
    module: &Module,
    function: FuncId,
    site: ObligationSite,
    variant: Variant,
    instantiate_havoc: bool,
    ones_seed: bool,
) -> Module {
    let mut built = module.clone();
    built.functions.retain(|candidate| candidate.id == function);
    let signature = built
        .func_type(built.functions[0].ty)
        .cloned()
        .expect("signature exists");
    let void_ty = FuncTyId::new(built.func_types.len() as u32);
    built.func_types.push(FuncTy {
        params: signature.params,
        returns: Vec::new(),
        is_vararg: false,
        abi: None,
    });
    let order = chain(module, function);
    let cut = order
        .iter()
        .position(|block| *block == site.block)
        .expect("site is on the chain");
    let keep = order[..=cut].iter().copied().collect::<BTreeSet<_>>();

    let target = &mut built.functions[0];
    target.ty = void_ty;
    target.blocks.retain(|block| keep.contains(&block.id));
    let mut next_value = target.max_value_id() + 1;
    for block in &mut target.blocks {
        if block.id == site.block {
            block.body.truncate(site.inst_index as usize + 1);
            block
                .body
                .push(InstrNode::new(Inst::Return { values: Vec::new() }));
        }
        for index in 0..block.body.len() {
            let is_site = block.id == site.block && index == site.inst_index as usize;
            let node = &mut block.body[index];
            if let Inst::Undef {
                ty: Ty::Tuple(fields),
            } = node.inst.clone()
            {
                if !instantiate_havoc {
                    continue;
                }
                let seeded = fields
                    .iter()
                    .map(|ty| match (ty, ones_seed) {
                        (Ty::Bool, ones) => Constant::Bool(ones),
                        (Ty::U8, true) => Constant::Int(255),
                        (Ty::I8, true) => Constant::Int(-128),
                        (_, true) => Constant::Int(1),
                        (_, false) => Constant::Int(0),
                    })
                    .collect();
                node.inst = Inst::Const {
                    ty: Ty::Tuple(fields),
                    value: Constant::Aggregate(seeded),
                };
                continue;
            }
            if let Inst::Assert { cond, .. } = node.inst {
                let keep_assert = match variant {
                    Variant::Site => is_site,
                    Variant::Pre => false,
                    Variant::Prior => !is_site,
                };
                if !keep_assert {
                    node.inst = Inst::Copy {
                        ty: Ty::Bool,
                        operand: cond,
                    };
                    node.results = vec![ValueId::new(next_value)];
                    next_value += 1;
                }
            }
        }
    }
    built
}

/// Whether an `Inst::Undef` is executed on the way to `site`, derived here
/// from this file's own chain walk rather than from the lane's report.
fn havoc_seed_precedes(module: &Module, function: FuncId, site: ObligationSite) -> bool {
    let target = module.function_by_id(function).expect("function exists");
    for block_id in chain(module, function) {
        let block = target
            .blocks
            .iter()
            .find(|block| block.id == block_id)
            .expect("chain block exists");
        for (index, node) in block.body.iter().enumerate() {
            if block_id == site.block && index >= site.inst_index as usize {
                return false;
            }
            if matches!(node.inst, Inst::Undef { .. }) {
                return true;
            }
        }
    }
    false
}

fn execute(module: &Module, function: FuncId, args: Vec<InterpretValue>) -> Outcome {
    let options = InterpretOptions {
        fuel: 1_000_000,
        ..InterpretOptions::default()
    };
    match Interpreter::with_module(module)
        .with_options(options)
        .execute_func(function, args)
    {
        Ok(_) => Outcome::Reached,
        Err(error) => match error.code {
            InterpretErrorCode::Panic => Outcome::Panic,
            InterpretErrorCode::UndefinedBehavior => Outcome::UndefinedBehavior,
            InterpretErrorCode::AssumeViolated => Outcome::AssumeViolated,
            other => Outcome::Other(format!("{other}: {error}")),
        },
    }
}

fn param_types(module: &Module, function: FuncId) -> Vec<Ty> {
    let target = module.function_by_id(function).expect("function exists");
    module
        .func_type(target.ty)
        .expect("signature exists")
        .params
        .clone()
}

/// Every value of an 8-bit (or Bool) parameter.
fn domain(ty: &Ty) -> Vec<InterpretValue> {
    match ty {
        Ty::U8 => (0..=255i128)
            .map(|v| InterpretValue::int(Ty::U8, v).expect("u8"))
            .collect(),
        Ty::I8 => (-128..=127i128)
            .map(|v| InterpretValue::int(Ty::I8, v).expect("i8"))
            .collect(),
        Ty::Bool => vec![InterpretValue::bool(false), InterpretValue::bool(true)],
        other => panic!("{other} is not exhaustively enumerable"),
    }
}

fn cartesian(types: &[Ty]) -> Vec<Vec<InterpretValue>> {
    let mut rows = vec![Vec::new()];
    for ty in types {
        let values = domain(ty);
        let mut next = Vec::with_capacity(rows.len() * values.len());
        for row in &rows {
            for value in &values {
                let mut extended = row.clone();
                extended.push(value.clone());
                next.push(extended);
            }
        }
        rows = next;
    }
    rows
}

fn witness_args(witness: &TrustIrBodyWitness) -> Vec<InterpretValue> {
    witness
        .params
        .iter()
        .map(|(_, scalar)| match scalar {
            TrustIrScalar::Bool(b) => InterpretValue::bool(*b),
            TrustIrScalar::Int { ty, value } => {
                InterpretValue::int(ty.clone(), *value).expect("witness is typed")
            }
        })
        .collect()
}

#[derive(Default, Debug)]
struct Counters {
    fixtures: usize,
    obligations: usize,
    inputs: usize,
    executions: usize,
    havoc_sites: usize,
    pinned_sites: usize,
}

fn check_fixture(fixture: &Fixture, counters: &mut Counters) {
    let function = fixture.function();
    let report = TrustVcTrustEngine::new()
        .discharge_trust_ir_function(&fixture.module, function, &TrustIrBodyOptions::default())
        .unwrap_or_else(|error| panic!("{}: {error}", fixture.name));
    assert!(
        report.function_refusal.is_none(),
        "{}: the oracle only covers admitted bodies, got {:?}",
        fixture.name,
        report.function_refusal
    );
    counters.fixtures += 1;

    let types = param_types(&fixture.module, function);
    let inputs = cartesian(&types);

    for obligation in &report.obligations {
        let site = obligation.site.expect("oracle fixtures carry sites");
        counters.obligations += 1;
        counters.inputs += inputs.len();

        // Which semantics is this agreement about? Derived independently, and
        // required to match what the lane declares.
        let expected_reading = if havoc_seed_precedes(&fixture.module, function, site) {
            BodyReading::HavocInstantiatedUndef
        } else {
            BodyReading::PinnedInterpreter
        };
        assert_eq!(
            obligation.reading, expected_reading,
            "{} {site:?}: the lane's declared reading disagrees with the oracle's",
            fixture.name
        );
        if expected_reading == BodyReading::HavocInstantiatedUndef {
            counters.havoc_sites += 1;
            assert!(
                !report.havoc_seeds.is_empty(),
                "{} {site:?}: a havoc-instantiated site must list its seeds",
                fixture.name
            );
        } else {
            counters.pinned_sites += 1;
            // Nothing was instantiated on the way to this site, so each
            // variant below is a literal sub-program of the module the
            // obligation is about: the agreement really is with the pinned
            // semantics. Proved structurally, by rebuilding every variant with
            // the havoc rewrite disabled and requiring an identical module.
            for variant in [Variant::Site, Variant::Pre, Variant::Prior] {
                assert_eq!(
                    variant_module_inner(&fixture.module, function, site, variant, true),
                    variant_module_inner(&fixture.module, function, site, variant, false),
                    "{} {site:?}: claimed the pinned reading, but the {variant:?} variant rewrote an Undef",
                    fixture.name
                );
            }
        }

        let site_module = variant_module(&fixture.module, function, site, Variant::Site);
        let pre_module = variant_module(&fixture.module, function, site, Variant::Pre);
        let prior_module = variant_module(&fixture.module, function, site, Variant::Prior);

        let mut panicking = 0usize;
        let mut reaching = 0usize;
        for input in &inputs {
            let site_outcome = execute(&site_module, function, input.clone());
            let pre_outcome = execute(&pre_module, function, input.clone());
            counters.executions += 2;
            for outcome in [&site_outcome, &pre_outcome] {
                if let Outcome::Other(detail) = outcome {
                    panic!("{} {site:?}: interpreter said {detail}", fixture.name);
                }
            }
            if site_outcome == Outcome::Panic {
                panicking += 1;
            }
            if pre_outcome == Outcome::Reached {
                reaching += 1;
            }
        }

        match &obligation.verdict {
            TrustIrBodyVerdict::DischargedAdvisory {
                premise_witness, ..
            } => {
                assert_eq!(
                    panicking, 0,
                    "{} {site:?}: discharged, but {panicking} inputs panic the site",
                    fixture.name
                );
                assert!(
                    reaching > 0,
                    "{} {site:?}: discharged with no input reaching the site",
                    fixture.name
                );
                counters.executions += 1;
                assert_eq!(
                    execute(&pre_module, function, witness_args(premise_witness)),
                    Outcome::Reached,
                    "{} {site:?}: the reported premise witness does not reach the site",
                    fixture.name
                );
            }
            TrustIrBodyVerdict::Refuted { witness } => {
                assert!(
                    panicking > 0,
                    "{} {site:?}: refuted, but no input panics the site",
                    fixture.name
                );
                counters.executions += 2;
                assert_eq!(
                    execute(&site_module, function, witness_args(witness)),
                    Outcome::Panic,
                    "{} {site:?}: the reported witness does not fail the site",
                    fixture.name
                );
                assert_eq!(
                    execute(&prior_module, function, witness_args(witness)),
                    Outcome::Reached,
                    "{} {site:?}: a plain refutation must pass every earlier assert",
                    fixture.name
                );
            }
            TrustIrBodyVerdict::RefutedIgnoringPriorAsserts { witness } => {
                assert!(
                    panicking > 0,
                    "{} {site:?}: refuted, but no input panics the site",
                    fixture.name
                );
                counters.executions += 2;
                assert_eq!(
                    execute(&site_module, function, witness_args(witness)),
                    Outcome::Panic,
                    "{} {site:?}: the reported witness does not fail the site",
                    fixture.name
                );
                assert_eq!(
                    execute(&prior_module, function, witness_args(witness)),
                    Outcome::Panic,
                    "{} {site:?}: this label claims an earlier assert fails first",
                    fixture.name
                );
            }
            TrustIrBodyVerdict::NotAnswerable(TrustIrBodyRefusal::VacuousPremises) => {
                assert_eq!(
                    reaching, 0,
                    "{} {site:?}: called vacuous, but {reaching} inputs reach the site",
                    fixture.name
                );
            }
            other => panic!(
                "{} {site:?}: the oracle's fixtures must all be decided, got {other:?}",
                fixture.name
            ),
        }

        // Completeness pin, in the other direction: what the interpreter
        // found dictates which verdict is admissible at all.
        let verdict = &obligation.verdict;
        if reaching == 0 {
            assert!(
                matches!(
                    verdict,
                    TrustIrBodyVerdict::NotAnswerable(TrustIrBodyRefusal::VacuousPremises)
                ),
                "{} {site:?}: no input reaches the site, so the premises are vacuous",
                fixture.name
            );
        } else if panicking == 0 {
            assert!(
                verdict.is_discharged_advisory(),
                "{} {site:?}: no input panics the site, so it must be discharged",
                fixture.name
            );
        } else {
            assert!(
                matches!(
                    verdict,
                    TrustIrBodyVerdict::Refuted { .. }
                        | TrustIrBodyVerdict::RefutedIgnoringPriorAsserts { .. }
                ),
                "{} {site:?}: {panicking} inputs panic the site, so it must be refuted",
                fixture.name
            );
        }
    }
}

fn eight_bit_fixtures() -> Vec<Fixture> {
    vec![
        fixtures::guarded_checked_add_u8(),
        fixtures::guarded_checked_add_i8(),
        fixtures::two_checks_chain(),
        fixtures::wraparound_semantics(),
        fixtures::expected_true_shape(),
        fixtures::br_param_binding(false),
        fixtures::br_param_binding(true),
        fixtures::unguarded_checked_op("oracle_add_u8", OverflowOp::AddOverflow, Ty::U8),
        fixtures::unguarded_checked_op("oracle_sub_u8", OverflowOp::SubOverflow, Ty::U8),
        fixtures::unguarded_checked_op("oracle_mul_u8", OverflowOp::MulOverflow, Ty::U8),
        fixtures::unguarded_checked_op("oracle_add_i8", OverflowOp::AddOverflow, Ty::I8),
        fixtures::unguarded_checked_op("oracle_sub_i8", OverflowOp::SubOverflow, Ty::I8),
        fixtures::unguarded_checked_op("oracle_mul_i8", OverflowOp::MulOverflow, Ty::I8),
        fixtures::unguarded_with_producer_claims(),
        fixtures::assume_after_assert(),
        fixtures::assumes_in_later_block(),
        fixtures::contradictory_later_assume(),
        fixtures::vacuous_prefix(0),
        fixtures::vacuous_prefix(1),
        fixtures::pinned_operands_add(Ty::U8, "oracle_pinned_u8"),
        fixtures::pinned_operands_add(Ty::I8, "oracle_pinned_i8"),
        fixtures::sign_of_all_ones(Ty::I8, -1, "oracle_all_ones_i8"),
        fixtures::sign_of_all_ones(Ty::U8, 255, "oracle_all_ones_u8"),
        fixtures::prior_asserts_guard_the_add(),
        fixtures::unobligated_assert_present(),
    ]
}

#[test]
fn the_lane_agrees_with_the_reference_interpreter_over_every_eight_bit_input() {
    let mut counters = Counters::default();
    for fixture in eight_bit_fixtures() {
        check_fixture(&fixture, &mut counters);
    }
    println!(
        "trust-ir body lane oracle: {} fixtures, {} obligations ({} havoc-instantiated, {} pinned), {} enumerated inputs, {} interpreter executions",
        counters.fixtures,
        counters.obligations,
        counters.havoc_sites,
        counters.pinned_sites,
        counters.inputs,
        counters.executions
    );
    assert!(counters.obligations >= 25, "{counters:?}");
    assert!(counters.inputs >= 1_000_000, "{counters:?}");
    // Both readings must be exercised: a corpus that drifted to one of them
    // would quietly stop testing the other.
    assert!(counters.havoc_sites > 0, "{counters:?}");
    assert!(counters.pinned_sites > 0, "{counters:?}");
}

/// The havoc admission is an over-approximation only because the particular
/// value chosen for `Inst::Undef` is UNOBSERVABLE: the checker refuses every
/// read of a field no `InsertField` wrote, and an aggregate cannot be used
/// where a scalar is required. So a verdict — a refutation in particular —
/// holds for EVERY instantiation of the havoc, not just for the one the replay
/// happened to pick. Measured here by replaying each variant under a second,
/// deliberately different seeding and requiring identical outcomes on every
/// input.
#[test]
fn the_choice_of_havoc_instantiation_is_unobservable() {
    let fixtures = [
        fixtures::guarded_checked_add_u8(),
        fixtures::unguarded_checked_op("seed_probe_add_u8", OverflowOp::AddOverflow, Ty::U8),
        fixtures::unguarded_checked_op("seed_probe_mul_i8", OverflowOp::MulOverflow, Ty::I8),
        fixtures::two_checks_chain(),
    ];
    let mut compared = 0usize;
    let mut seeded_sites = 0usize;
    for fixture in &fixtures {
        let function = fixture.function();
        let report = TrustVcTrustEngine::new()
            .discharge_trust_ir_function(&fixture.module, function, &TrustIrBodyOptions::default())
            .unwrap_or_else(|error| panic!("{}: {error}", fixture.name));
        let inputs = cartesian(&param_types(&fixture.module, function));
        for obligation in &report.obligations {
            let site = obligation.site.expect("fixture sites");
            assert_eq!(
                obligation.reading,
                BodyReading::HavocInstantiatedUndef,
                "{}: this probe is only meaningful on a havoc-seeded site",
                fixture.name
            );
            seeded_sites += 1;
            for variant in [Variant::Site, Variant::Pre, Variant::Prior] {
                let zeros =
                    variant_module_seeded(&fixture.module, function, site, variant, true, false);
                let ones =
                    variant_module_seeded(&fixture.module, function, site, variant, true, true);
                assert_ne!(
                    zeros, ones,
                    "{}: the two seedings must actually differ",
                    fixture.name
                );
                for input in &inputs {
                    assert_eq!(
                        execute(&zeros, function, input.clone()),
                        execute(&ones, function, input.clone()),
                        "{} {site:?} {variant:?}: the havoc instantiation is observable on {input:?}",
                        fixture.name
                    );
                    compared += 1;
                }
            }
        }
    }
    println!(
        "trust-ir body lane havoc probe: {seeded_sites} seeded sites, {compared} paired executions"
    );
    assert!(seeded_sites >= 5, "{seeded_sites}");
    assert!(compared >= 500_000, "{compared}");
}
