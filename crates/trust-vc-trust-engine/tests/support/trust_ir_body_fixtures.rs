// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Hand-built trust-ir fixtures, including the bridge's historical checked pack.
//!
//! NOT Trust-emitted. These modules were written against trust-ir
//! `0.11.0@4803c40` (binary v38), and are measured at `0.14.0@4f09dab8`
//! (binary v46), by mirroring the then-current `~/trust` `origin/main`
//! `crates/trust-ir-bridge/src/lower.rs`:
//!
//! * a `#[trust::requires]` clause is `Const` + `ICmp` + `Assume` in the entry
//!   block (lower.rs:1759-1775, :1843-1896);
//! * a MIR `CheckedBinaryOp` is `Overflow` (annotated `NoOverflow`) followed
//!   by `Undef Tuple` (annotated `FreshSymbolicHavoc`) + two `InsertField`
//!   (lower.rs:32974-33265);
//! * a `Terminator::Assert` with `expected = false` is `ExtractField .1` +
//!   `Const Bool false` + `ICmp Eq Bool` + `Assert` + a SITED obligation +
//!   `Br` (lower.rs:37799-37820, :6177-6220);
//! * only the ENTRY block takes `Br` arguments (lower.rs:3368-3378), so
//!   values cross blocks by dominance. `br_param_binding` deliberately breaks
//!   that to exercise parameter binding anyway.
//!
//! `target_info` is `None` (target-independent), which is one of the two
//! layouts trust-ir's reference interpreter executes.
//!
//! The legacy `Undef` packs intentionally remain for havoc/UB regressions;
//! they are not the bridge's current complete-construction spelling. The
//! `trust_ir_body_aggregate` tests build `MakeAggregate` tuples directly and
//! check the module-as-written reading, declaration order and false claims.

#![allow(dead_code)]

use trust_ir::{
    AssertKind, BinOp, Block, BlockId, CallingConv, Constant, FuncAttrs, FuncId, FuncTy, FuncTyId,
    Function, ICmpOp, Inst, InstrNode, Linkage, Module, ObligationKind, ObligationSite, OverflowOp,
    ProofAnnotation, ProofFormula, ProofId, ProofObligation, ProofObligationSourceIdentity,
    ProofStatus, Ty, ValueId,
};

pub const FIXTURE_FUNCTION: FuncId = FuncId(0);

/// A fixture module plus the obligations it declares, in creation order.
pub struct Fixture {
    pub name: &'static str,
    pub module: Module,
    pub obligations: Vec<ProofId>,
}

impl Fixture {
    pub fn function(&self) -> FuncId {
        FIXTURE_FUNCTION
    }
}

pub struct Fx {
    name: &'static str,
    module: Module,
    blocks: Vec<Block>,
    current: usize,
    next_value: u32,
    obligations: Vec<ProofId>,
}

impl Fx {
    /// Start a function `(params) -> returns` with the entry block bb0 whose
    /// parameters are `%0..`.
    pub fn new(name: &'static str, params: &[Ty], returns: &[Ty]) -> (Self, Vec<ValueId>) {
        let mut module = Module::new(name);
        module.func_types.push(FuncTy {
            params: params.to_vec(),
            returns: returns.to_vec(),
            is_vararg: false,
            abi: None,
        });
        let mut entry = Block::new(BlockId::new(0));
        let mut values = Vec::new();
        for (index, ty) in params.iter().enumerate() {
            let value = ValueId::new(index as u32);
            entry.params.push((value, ty.clone()));
            values.push(value);
        }
        let fx = Self {
            name,
            module,
            blocks: vec![entry],
            current: 0,
            next_value: params.len() as u32,
            obligations: Vec::new(),
        };
        (fx, values)
    }

    pub fn fresh(&mut self) -> ValueId {
        let value = ValueId::new(self.next_value);
        self.next_value += 1;
        value
    }

    pub fn current_block(&self) -> BlockId {
        self.blocks[self.current].id
    }

    /// Append `node` to the current block and return its `(block, index)`.
    pub fn push(&mut self, node: InstrNode) -> (BlockId, u32) {
        let block = &mut self.blocks[self.current];
        let index = block.body.len() as u32;
        block.body.push(node);
        (block.id, index)
    }

    fn push_value(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh();
        self.push(InstrNode::new(inst).with_result(result));
        result
    }

    pub fn konst(&mut self, ty: Ty, value: i128) -> ValueId {
        self.push_value(Inst::Const {
            ty,
            value: Constant::Int(value),
        })
    }

    pub fn bool_const(&mut self, value: bool) -> ValueId {
        self.push_value(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(value),
        })
    }

    pub fn icmp(&mut self, op: ICmpOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.push_value(Inst::ICmp { op, ty, lhs, rhs })
    }

    pub fn binop(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.push_value(Inst::BinOp { op, ty, lhs, rhs })
    }

    pub fn copy(&mut self, ty: Ty, operand: ValueId) -> ValueId {
        self.push_value(Inst::Copy { ty, operand })
    }

    pub fn assume(&mut self, cond: ValueId) -> (BlockId, u32) {
        self.push(InstrNode::new(Inst::Assume { cond }))
    }

    /// `#[trust::requires]`-shaped clause: `Const k` + `ICmp op value k` +
    /// `Assume`.
    pub fn requires(&mut self, value: ValueId, op: ICmpOp, ty: Ty, k: i128) -> ValueId {
        let konst = self.konst(ty.clone(), k);
        let cond = self.icmp(op, ty, value, konst);
        self.assume(cond);
        cond
    }

    /// `requires` over two values (no constant), e.g. `a >=u b`.
    pub fn requires_pair(&mut self, lhs: ValueId, op: ICmpOp, ty: Ty, rhs: ValueId) -> ValueId {
        let cond = self.icmp(op, ty, lhs, rhs);
        self.assume(cond);
        cond
    }

    /// MIR `CheckedBinaryOp`: `Overflow` + `Undef Tuple` + two `InsertField`.
    /// Returns the packed `(T, bool)` tuple value.
    pub fn checked_op(&mut self, op: OverflowOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        let tuple_ty = Ty::Tuple(vec![ty.clone(), Ty::Bool]);
        let value = self.fresh();
        let flag = self.fresh();
        self.push(
            InstrNode::new(Inst::Overflow {
                op,
                ty: ty.clone(),
                lhs,
                rhs,
            })
            .with_result(value)
            .with_result(flag)
            .with_proof(ProofAnnotation::NoOverflow),
        );
        let seed = self.fresh();
        self.push(
            InstrNode::new(Inst::Undef {
                ty: tuple_ty.clone(),
            })
            .with_result(seed)
            .with_proof(ProofAnnotation::FreshSymbolicHavoc),
        );
        let with_value = self.push_value(Inst::InsertField {
            ty: tuple_ty.clone(),
            aggregate: seed,
            field: 0,
            value,
        });
        self.push_value(Inst::InsertField {
            ty: tuple_ty,
            aggregate: with_value,
            field: 1,
            value: flag,
        })
    }

    pub fn extract(&mut self, ty: Ty, aggregate: ValueId, field: u32) -> ValueId {
        self.push_value(Inst::ExtractField {
            ty,
            aggregate,
            field,
        })
    }

    /// The `Terminator::Assert { expected: false }` shape over a checked-op
    /// tuple, with the obligation Trust's `add_obligation_for_last_inst`
    /// attaches.
    pub fn mir_assert(&mut self, tuple: ValueId, kind: ObligationKind) -> ProofId {
        let flag = self.extract(Ty::Bool, tuple, 1);
        let expected = self.bool_const(false);
        let cond = self.icmp(ICmpOp::Eq, Ty::Bool, flag, expected);
        let site = self.push(InstrNode::new(Inst::Assert {
            cond,
            kind: AssertKind::Unspecified,
            site: None,
        }));
        self.obligation_at(site, kind)
    }

    /// The same shape WITHOUT an obligation row — Trust's
    /// `UncheckedBinaryOp` (lower.rs:35200-35240).
    pub fn mir_assert_unobligated(&mut self, tuple: ValueId) -> (BlockId, u32) {
        let flag = self.extract(Ty::Bool, tuple, 1);
        let expected = self.bool_const(false);
        let cond = self.icmp(ICmpOp::Eq, Ty::Bool, flag, expected);
        self.push(InstrNode::new(Inst::Assert {
            cond,
            kind: AssertKind::Unspecified,
            site: None,
        }))
    }

    /// A bare `Assert` on an already-Bool condition, with an obligation.
    pub fn assert_obligated(&mut self, cond: ValueId, kind: ObligationKind) -> ProofId {
        let site = self.push(InstrNode::new(Inst::Assert {
            cond,
            kind: AssertKind::Unspecified,
            site: None,
        }));
        self.obligation_at(site, kind)
    }

    pub fn assert_bare(&mut self, cond: ValueId) -> (BlockId, u32) {
        self.push(InstrNode::new(Inst::Assert {
            cond,
            kind: AssertKind::Unspecified,
            site: None,
        }))
    }

    pub fn obligation_at(&mut self, site: (BlockId, u32), kind: ObligationKind) -> ProofId {
        let id = ProofId::new(self.module.proof_obligations.len() as u32);
        let index = id.index();
        self.module.proof_obligations.push(ProofObligation {
            id,
            kind,
            status: ProofStatus::Pending,
            description: format!("{} obligation {index}", self.name),
            formula: Some(ProofFormula::new(
                "trust-types.Formula@1",
                format!("{{\"fixture\":\"{}\",\"obligation\":{index}}}", self.name),
            )),
            function: Some(FIXTURE_FUNCTION),
            source: Some(ProofObligationSourceIdentity::new(
                format!("fixture/{}.rs", self.name),
                format!("{}::obligation{index}", self.name),
            )),
            site: Some(ObligationSite::new(FIXTURE_FUNCTION, site.0, site.1)),
            spec: None,
        });
        self.obligations.push(id);
        id
    }

    /// Declare a new block (it does not become current).
    pub fn block(&mut self, params: &[Ty]) -> (BlockId, Vec<ValueId>) {
        let id = BlockId::new(self.blocks.len() as u32);
        let mut block = Block::new(id);
        let mut values = Vec::new();
        for ty in params {
            let value = self.fresh();
            block.params.push((value, ty.clone()));
            values.push(value);
        }
        self.blocks.push(block);
        (id, values)
    }

    pub fn switch_to(&mut self, block: BlockId) {
        self.current = self
            .blocks
            .iter()
            .position(|candidate| candidate.id == block)
            .expect("fixture block exists");
    }

    pub fn goto(&mut self, target: BlockId, args: &[ValueId]) -> (BlockId, u32) {
        self.push(InstrNode::new(Inst::Br {
            target,
            args: args.to_vec(),
        }))
    }

    pub fn ret(&mut self, values: &[ValueId]) -> (BlockId, u32) {
        self.push(InstrNode::new(Inst::Return {
            values: values.to_vec(),
        }))
    }

    pub fn module_mut(&mut self) -> &mut Module {
        &mut self.module
    }

    pub fn finish(mut self) -> Fixture {
        let function = Function {
            id: FIXTURE_FUNCTION,
            name: self.name.to_string(),
            ty: FuncTyId::new(0),
            entry: BlockId::new(0),
            blocks: std::mem::take(&mut self.blocks),
            proofs: Vec::new(),
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            attrs: FuncAttrs::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
            // trust-ir v41/v45 link metadata: no claim, as Trust's bridge
            // emits for an ordinary body.
            body_gate: None,
            display_path: None,
            section: None,
            visibility: trust_ir::Visibility::default(),
            retained: false,
        };
        self.module.functions.push(function);
        Fixture {
            name: self.name,
            module: self.module,
            obligations: self.obligations,
        }
    }
}

// ---------------------------------------------------------------------------
// Positive fixtures
// ---------------------------------------------------------------------------

/// P1: `fn f(a: u8, b: u8) -> u8 { a + b }` with `requires a < 100, b < 100`.
pub fn guarded_checked_add_u8() -> Fixture {
    let (mut fx, params) = Fx::new("guarded_checked_add_u8", &[Ty::U8, Ty::U8], &[Ty::U8]);
    let (a, b) = (params[0], params[1]);
    fx.requires(a, ICmpOp::Ult, Ty::U8, 100);
    fx.requires(b, ICmpOp::Ult, Ty::U8, 100);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    let (exit, _) = fx.block(&[]);
    fx.goto(exit, &[]);
    fx.switch_to(exit);
    let sum = fx.extract(Ty::U8, tuple, 0);
    fx.ret(&[sum]);
    fx.finish()
}

/// P2: the same over `i8` with signed guards.
pub fn guarded_checked_add_i8() -> Fixture {
    let (mut fx, params) = Fx::new("guarded_checked_add_i8", &[Ty::I8, Ty::I8], &[Ty::I8]);
    let (a, b) = (params[0], params[1]);
    fx.requires(a, ICmpOp::Slt, Ty::I8, 50);
    fx.requires(a, ICmpOp::Sgt, Ty::I8, -50);
    fx.requires(b, ICmpOp::Slt, Ty::I8, 50);
    fx.requires(b, ICmpOp::Sgt, Ty::I8, -50);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::I8, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    let (exit, _) = fx.block(&[]);
    fx.goto(exit, &[]);
    fx.switch_to(exit);
    let sum = fx.extract(Ty::I8, tuple, 0);
    fx.ret(&[sum]);
    fx.finish()
}

/// P3: two checked ops over three blocks, the second reading the first's
/// result across a block boundary by dominance.
pub fn two_checks_chain() -> Fixture {
    let (mut fx, params) = Fx::new("two_checks_chain", &[Ty::U8, Ty::U8], &[Ty::U8]);
    let (a, b) = (params[0], params[1]);
    fx.requires(a, ICmpOp::Ult, Ty::U8, 10);
    fx.requires(b, ICmpOp::Ult, Ty::U8, 10);
    let sum_tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, b);
    fx.mir_assert(sum_tuple, ObligationKind::ArithmeticSafety);
    let (middle, _) = fx.block(&[]);
    fx.goto(middle, &[]);
    fx.switch_to(middle);
    let sum = fx.extract(Ty::U8, sum_tuple, 0);
    let product_tuple = fx.checked_op(OverflowOp::MulOverflow, Ty::U8, sum, b);
    fx.mir_assert(product_tuple, ObligationKind::ArithmeticSafety);
    let (exit, _) = fx.block(&[]);
    fx.goto(exit, &[]);
    fx.switch_to(exit);
    let product = fx.extract(Ty::U8, product_tuple, 0);
    fx.ret(&[product]);
    fx.finish()
}

/// P4: constant wrap-around. `200 + 100 == 44` at `u8`, and `> 200` is false.
pub fn wraparound_semantics() -> Fixture {
    let (mut fx, _params) = Fx::new("wraparound_semantics", &[Ty::U8], &[]);
    let two_hundred = fx.konst(Ty::U8, 200);
    let hundred = fx.konst(Ty::U8, 100);
    let wrapped = fx.binop(BinOp::Add, Ty::U8, two_hundred, hundred);
    let forty_four = fx.konst(Ty::U8, 44);
    let is_44 = fx.icmp(ICmpOp::Eq, Ty::U8, wrapped, forty_four);
    fx.assert_obligated(is_44, ObligationKind::PanicFreedom);
    let gt_200 = fx.icmp(ICmpOp::Ugt, Ty::U8, wrapped, two_hundred);
    fx.assert_obligated(gt_200, ObligationKind::PanicFreedom);
    fx.ret(&[]);
    fx.finish()
}

/// P5: an `Assert` directly on an `ICmp` result (a bounds check).
pub fn expected_true_shape() -> Fixture {
    let (mut fx, params) = Fx::new("expected_true_shape", &[Ty::U8], &[]);
    let a = params[0];
    fx.requires(a, ICmpOp::Ult, Ty::U8, 10);
    let sixteen = fx.konst(Ty::U8, 16);
    let in_bounds = fx.icmp(ICmpOp::Ult, Ty::U8, a, sixteen);
    fx.assert_obligated(in_bounds, ObligationKind::BoundsCheck);
    fx.ret(&[]);
    fx.finish()
}

/// P6: `Br` parameter binding. Trust never passes args to a non-entry block;
/// v0 admits it anyway, so it is pinned here. `swap` sends the arguments in
/// the wrong order, which the asymmetric guard `a >= b` then refutes.
pub fn br_param_binding(swap: bool) -> Fixture {
    let name = if swap {
        "br_param_binding_swapped"
    } else {
        "br_param_binding"
    };
    let (mut fx, params) = Fx::new(name, &[Ty::U8, Ty::U8], &[Ty::U8]);
    let (a, b) = (params[0], params[1]);
    fx.requires_pair(a, ICmpOp::Uge, Ty::U8, b);
    let (body, body_params) = fx.block(&[Ty::U8, Ty::U8]);
    if swap {
        fx.goto(body, &[b, a]);
    } else {
        fx.goto(body, &[a, b]);
    }
    fx.switch_to(body);
    let (x, y) = (body_params[0], body_params[1]);
    let tuple = fx.checked_op(OverflowOp::SubOverflow, Ty::U8, x, y);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    let difference = fx.extract(Ty::U8, tuple, 0);
    fx.ret(&[difference]);
    fx.finish()
}

// ---------------------------------------------------------------------------
// Liars
// ---------------------------------------------------------------------------

/// L1: P1 with no guards at all.
pub fn unguarded_checked_op(name: &'static str, op: OverflowOp, ty: Ty) -> Fixture {
    let (mut fx, params) = Fx::new(name, &[ty.clone(), ty.clone()], std::slice::from_ref(&ty));
    let (a, b) = (params[0], params[1]);
    let tuple = fx.checked_op(op, ty.clone(), a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    let (exit, _) = fx.block(&[]);
    fx.goto(exit, &[]);
    fx.switch_to(exit);
    let result = fx.extract(ty, tuple, 0);
    fx.ret(&[result]);
    fx.finish()
}

pub fn unguarded_checked_add_u8() -> Fixture {
    unguarded_checked_op("unguarded_checked_add_u8", OverflowOp::AddOverflow, Ty::U8)
}

/// L9: the unguarded body PLUS every claim a producer could stamp on it —
/// `NoOverflow` on the node, function-level annotations, a proved summary.
pub fn unguarded_with_producer_claims() -> Fixture {
    let mut fixture = unguarded_checked_op(
        "unguarded_with_producer_claims",
        OverflowOp::AddOverflow,
        Ty::U8,
    );
    let function = &mut fixture.module.functions[0];
    function.proofs.push(ProofAnnotation::NoOverflow);
    function.proofs.push(ProofAnnotation::Pure);
    function.summary = Some(trust_ir::FunctionSummary {
        requires: vec![ProofFormula::new("trust-types.Formula@1", "\"a < 100\"")],
        ensures: vec![ProofFormula::new("trust-types.Formula@1", "\"true\"")],
        params: vec!["a".to_string(), "b".to_string()],
        proved: true,
        decreases: Vec::new(),
        // A bare `proved: true` with no backing: exactly the unauthenticated
        // producer claim this fixture exists to show is ignored.
        backed_by: None,
        effects: None,
    });
    fixture
}

/// L2: the guards are moved AFTER the site, in the same block.
pub fn assume_after_assert() -> Fixture {
    let (mut fx, params) = Fx::new("assume_after_assert", &[Ty::U8, Ty::U8], &[]);
    let (a, b) = (params[0], params[1]);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.requires(a, ICmpOp::Ult, Ty::U8, 100);
    fx.requires(b, ICmpOp::Ult, Ty::U8, 100);
    fx.ret(&[]);
    fx.finish()
}

/// L3: the guards are in the block AFTER the site.
pub fn assumes_in_later_block() -> Fixture {
    let (mut fx, params) = Fx::new("assumes_in_later_block", &[Ty::U8, Ty::U8], &[]);
    let (a, b) = (params[0], params[1]);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    let (exit, _) = fx.block(&[]);
    fx.goto(exit, &[]);
    fx.switch_to(exit);
    fx.requires(a, ICmpOp::Ult, Ty::U8, 100);
    fx.requires(b, ICmpOp::Ult, Ty::U8, 100);
    fx.ret(&[]);
    fx.finish()
}

/// L4: a contradictory `Assume` AFTER the site cannot make it vacuous.
pub fn contradictory_later_assume() -> Fixture {
    let (mut fx, params) = Fx::new("contradictory_later_assume", &[Ty::U8, Ty::U8], &[]);
    let (a, b) = (params[0], params[1]);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    let never = fx.bool_const(false);
    fx.assume(never);
    fx.ret(&[]);
    fx.finish()
}

/// L5: `a <u 0` is unsatisfiable, so the site is vacuous. `bound` = 1 is the
/// twin that IS satisfiable (only by `a == 0`).
pub fn vacuous_prefix(bound: i128) -> Fixture {
    let name = if bound == 0 {
        "vacuous_prefix"
    } else {
        "vacuous_prefix_twin"
    };
    let (mut fx, params) = Fx::new(name, &[Ty::U8, Ty::U8], &[]);
    let (a, b) = (params[0], params[1]);
    fx.requires(a, ICmpOp::Ult, Ty::U8, bound);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}

/// L11: `100 + 100` overflows `i8` but not `u8`.
pub fn pinned_operands_add(ty: Ty, name: &'static str) -> Fixture {
    let (mut fx, params) = Fx::new(name, &[ty.clone(), ty.clone()], &[]);
    let (a, b) = (params[0], params[1]);
    fx.requires(a, ICmpOp::Eq, ty.clone(), 100);
    fx.requires(b, ICmpOp::Eq, ty.clone(), 100);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, ty, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}

/// L11: the 0xFF bit pattern is `< 0` signed and `>= 0` unsigned, whichever
/// type the parameter carries. `pinned` is the value the guard fixes.
pub fn sign_of_all_ones(ty: Ty, pinned: i128, name: &'static str) -> Fixture {
    let (mut fx, params) = Fx::new(name, std::slice::from_ref(&ty), &[]);
    let x = params[0];
    fx.requires(x, ICmpOp::Eq, ty.clone(), pinned);
    let zero = fx.konst(ty.clone(), 0);
    let signed_lt = fx.icmp(ICmpOp::Slt, ty.clone(), x, zero);
    fx.assert_obligated(signed_lt, ObligationKind::PanicFreedom);
    let unsigned_lt = fx.icmp(ICmpOp::Ult, ty, x, zero);
    fx.assert_obligated(unsigned_lt, ObligationKind::PanicFreedom);
    fx.ret(&[]);
    fx.finish()
}

/// L13: two satisfiable `Assert`s guard an otherwise unguarded add. Every
/// overflowing input violates one of them, so the add can only be refuted by
/// IGNORING them.
pub fn prior_asserts_guard_the_add() -> Fixture {
    let (mut fx, params) = Fx::new("prior_asserts_guard_the_add", &[Ty::U8, Ty::U8], &[]);
    let (a, b) = (params[0], params[1]);
    let hundred = fx.konst(Ty::U8, 100);
    let a_small = fx.icmp(ICmpOp::Ult, Ty::U8, a, hundred);
    fx.assert_obligated(a_small, ObligationKind::PanicFreedom);
    let b_small = fx.icmp(ICmpOp::Ult, Ty::U8, b, hundred);
    fx.assert_obligated(b_small, ObligationKind::PanicFreedom);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}

/// L17: an `UncheckedBinaryOp`-shaped `Assert` with NO obligation row, ahead
/// of an obligated one.
pub fn unobligated_assert_present() -> Fixture {
    let (mut fx, params) = Fx::new("unobligated_assert_present", &[Ty::U8, Ty::U8], &[]);
    let (a, b) = (params[0], params[1]);
    fx.requires(a, ICmpOp::Ult, Ty::U8, 100);
    fx.requires(b, ICmpOp::Ult, Ty::U8, 100);
    let unchecked = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, b);
    fx.mir_assert_unobligated(unchecked);
    let checked = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, a, a);
    fx.mir_assert(checked, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}

/// A guarded checked add at a width wider than the oracle can enumerate.
pub fn guarded_wide_add(ty: Ty, bound: i128, signed: bool, name: &'static str) -> Fixture {
    let (mut fx, params) = Fx::new(name, &[ty.clone(), ty.clone()], &[]);
    let (a, b) = (params[0], params[1]);
    let (lt, gt) = if signed {
        (ICmpOp::Slt, ICmpOp::Sgt)
    } else {
        (ICmpOp::Ult, ICmpOp::Ugt)
    };
    fx.requires(a, lt, ty.clone(), bound);
    fx.requires(b, lt, ty.clone(), bound);
    if signed {
        fx.requires(a, gt, ty.clone(), -bound);
        fx.requires(b, gt, ty.clone(), -bound);
    }
    let tuple = fx.checked_op(OverflowOp::AddOverflow, ty, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}

/// A wide-width add pinned to exactly `(lhs, rhs)`.
pub fn pinned_wide_add(ty: Ty, lhs: i128, rhs: i128, name: &'static str) -> Fixture {
    let (mut fx, params) = Fx::new(name, &[ty.clone(), ty.clone()], &[]);
    let (a, b) = (params[0], params[1]);
    fx.requires(a, ICmpOp::Eq, ty.clone(), lhs);
    fx.requires(b, ICmpOp::Eq, ty.clone(), rhs);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, ty, a, b);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}

// ---------------------------------------------------------------------------
// Havoc-containment liars: every route out of the `Undef` pack
// ---------------------------------------------------------------------------

/// The real pack with the `InsertField` for field 1 dropped, so the
/// `ExtractField` reads a field nothing wrote — i.e. it would observe the
/// havoc seed. Must be refused.
pub fn extract_uninserted_field() -> Fixture {
    let (mut fx, params) = Fx::new("extract_uninserted_field", &[Ty::U8, Ty::U8], &[]);
    let (a, b) = (params[0], params[1]);
    let tuple_ty = Ty::Tuple(vec![Ty::U8, Ty::Bool]);
    let value = fx.fresh();
    let flag = fx.fresh();
    fx.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::U8,
            lhs: a,
            rhs: b,
        })
        .with_result(value)
        .with_result(flag),
    );
    let seed = fx.fresh();
    fx.push(
        InstrNode::new(Inst::Undef {
            ty: tuple_ty.clone(),
        })
        .with_result(seed)
        .with_proof(ProofAnnotation::FreshSymbolicHavoc),
    );
    let packed = fx.fresh();
    fx.push(
        InstrNode::new(Inst::InsertField {
            ty: tuple_ty,
            aggregate: seed,
            field: 0,
            value,
        })
        .with_result(packed),
    );
    // Field 1 was never written; reading it would read the havoc.
    fx.mir_assert(packed, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}

/// `Copy` of the pack: an aggregate cannot be copied as a scalar.
pub fn copy_the_pack() -> Fixture {
    let (mut fx, params) = Fx::new("copy_the_pack", &[Ty::U8, Ty::U8], &[]);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, params[0], params[1]);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.copy(Ty::Tuple(vec![Ty::U8, Ty::Bool]), tuple);
    fx.ret(&[]);
    fx.finish()
}

/// `Return` of the pack: the aggregate must not leave the function either.
pub fn return_the_pack() -> Fixture {
    let tuple_ty = Ty::Tuple(vec![Ty::U8, Ty::Bool]);
    let (mut fx, params) = Fx::new(
        "return_the_pack",
        &[Ty::U8, Ty::U8],
        std::slice::from_ref(&tuple_ty),
    );
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, params[0], params[1]);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.ret(&[tuple]);
    fx.finish()
}

/// `Assume` directly on the pack: the trust-ir `FreshSymbolicHavoc` contract
/// forbids narrowing the fresh value, and an `Assume` is exactly the operation
/// that doc names. It is refused as ill-typed before it can narrow anything.
pub fn assume_on_the_pack() -> Fixture {
    let (mut fx, params) = Fx::new("assume_on_the_pack", &[Ty::U8, Ty::U8], &[]);
    let tuple = fx.checked_op(OverflowOp::AddOverflow, Ty::U8, params[0], params[1]);
    fx.assume(tuple);
    fx.mir_assert(tuple, ObligationKind::ArithmeticSafety);
    fx.ret(&[]);
    fx.finish()
}
