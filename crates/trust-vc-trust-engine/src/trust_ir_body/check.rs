// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Structural, SSA and type check for the trust-ir body lane (v0).
//!
//! This is the lane's own admission gate. The direct advisory entry does not
//! run `trust-ir-build::validate_module` before reaching this checker. The
//! check therefore runs on EVERY call and refuses anything that is
//! not exactly the v0 shape: an acyclic chain of blocks joined by
//! unconditional `Br`, over the whitelisted instructions and scalar types.
//!
//! The output is the body flattened into chain order: one [`Step`] per
//! scalar definition, `Assume` and `Assert`, each tagged with its global
//! chain position. The lowering (`lower.rs`) reads nothing else.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncTy, Function, ICmpOp, Inst, InstrNode, Module, OverflowOp,
    Ty, ValueId,
};

use super::TrustIrBodyRefusal;

/// A scalar type admitted by v0.
///
/// `U128`/`I128` are deliberately absent: the overflow flag is computed at
/// twice the operand width, and 256-bit literals do not fit `i128`.
/// `Isize`/`Usize`/`Char` are absent because their width or valid range is a
/// target or validator claim v0 does not model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScalarTy {
    Int { bits: u32, signed: bool },
    Bool,
}

impl ScalarTy {
    pub(crate) fn from_ty(ty: &Ty) -> Option<Self> {
        let int = |bits, signed| Some(Self::Int { bits, signed });
        match ty {
            Ty::U8 => int(8, false),
            Ty::U16 => int(16, false),
            Ty::U32 => int(32, false),
            Ty::U64 => int(64, false),
            Ty::I8 => int(8, true),
            Ty::I16 => int(16, true),
            Ty::I32 => int(32, true),
            Ty::I64 => int(64, true),
            Ty::Bool => Some(Self::Bool),
            _ => None,
        }
    }

    pub(crate) fn to_ty(self) -> Ty {
        match self {
            Self::Bool => Ty::Bool,
            Self::Int { bits, signed } => match (bits, signed) {
                (8, false) => Ty::U8,
                (16, false) => Ty::U16,
                (32, false) => Ty::U32,
                (64, false) => Ty::U64,
                (8, true) => Ty::I8,
                (16, true) => Ty::I16,
                (32, true) => Ty::I32,
                (64, true) => Ty::I64,
                // `from_ty` is the only constructor outside this module and
                // never produces another width.
                _ => Ty::Error,
            },
        }
    }

    /// Inclusive value range of an integer type, `None` for `Bool` and for any
    /// width [`Self::from_ty`] cannot produce.
    ///
    /// `Self` is also minted at DOUBLE width inside `lower.rs` to encode the
    /// overflow flag, where 64-bit operands give `bits == 128`. That widened
    /// value is only ever handed to `lower::scalar_type`, never here or to
    /// [`Self::to_ty`] — this guard keeps a future caller that forgets from
    /// overflowing the shift, and its unit test pins it.
    pub(crate) fn int_bounds(self) -> Option<(i128, i128)> {
        let Self::Int { bits, signed } = self else {
            return None;
        };
        if !matches!(bits, 8 | 16 | 32 | 64) {
            return None;
        }
        if signed {
            let max = (1i128 << (bits - 1)) - 1;
            Some((-max - 1, max))
        } else {
            Some((0, (1i128 << bits) - 1))
        }
    }
}

/// The wrapping arithmetic v0 admits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ArithKind {
    Add,
    Sub,
    Mul,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoolKind {
    And,
    Or,
    Xor,
}

/// Right-hand side of one scalar definition `value == expr`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DefExpr {
    /// In-range integer constant (never relies on trust-ir's masking).
    IntConst(i128),
    BoolConst(bool),
    /// The shared IR's explicit scalar Bool connectives, never bitwise aliases.
    BoolBinary {
        op: BoolKind,
        lhs: ValueId,
        rhs: ValueId,
    },
    /// Width-`w` wrapping result of `BinOp` or of `Overflow`'s value result.
    Wrap {
        op: ArithKind,
        lhs: ValueId,
        rhs: ValueId,
    },
    /// `Overflow`'s flag result. Signedness comes from the operand TYPE.
    OverflowFlag {
        op: ArithKind,
        operand_ty: ScalarTy,
        lhs: ValueId,
        rhs: ValueId,
    },
    /// `ICmp`. Ordered signedness comes from the OP.
    ICmp {
        op: ICmpOp,
        operand_ty: ScalarTy,
        lhs: ValueId,
        rhs: ValueId,
    },
    /// `Copy`, `ExtractField` of a set field, and a `Br` parameter binding.
    Alias(ValueId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum StepKind {
    Def {
        value: ValueId,
        ty: ScalarTy,
        expr: DefExpr,
    },
    Assume {
        cond: ValueId,
    },
    Assert {
        cond: ValueId,
    },
}

/// One semantic step of the chain. `position` is the global index of the
/// instruction node in chain order; a `Br` parameter binding carries the
/// position of its `Br`, so it follows every node of the predecessor block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Step {
    pub(crate) position: usize,
    pub(crate) block: BlockId,
    pub(crate) inst_index: u32,
    pub(crate) kind: StepKind,
}

/// One admitted `Inst::Undef`, recorded because admitting it changes the
/// semantics the lane decides. See [`crate::trust_ir_body::BodyReading`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HavocSeed {
    pub(crate) position: usize,
    pub(crate) block: BlockId,
    pub(crate) inst_index: u32,
    pub(crate) ty: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckedBody {
    pub(crate) params: Vec<(ValueId, ScalarTy)>,
    pub(crate) steps: Vec<Step>,
    pub(crate) chain: Vec<BlockId>,
    pub(crate) positions: BTreeMap<(BlockId, u32), usize>,
    pub(crate) value_types: BTreeMap<ValueId, ScalarTy>,
    /// Every admitted `Inst::Undef`, in chain order.
    pub(crate) havoc_seeds: Vec<HavocSeed>,
}

impl CheckedBody {
    /// The `Assert` step at `(block, inst_index)`, if the node there is one.
    pub(crate) fn assert_at(&self, block: BlockId, inst_index: u32) -> Option<(usize, ValueId)> {
        self.steps.iter().find_map(|step| match step.kind {
            StepKind::Assert { cond } if step.block == block && step.inst_index == inst_index => {
                Some((step.position, cond))
            }
            _ => None,
        })
    }

    /// Whether a havoc seed is executed on the way to `position`, i.e. whether
    /// the verdict for that site is measured on a havoc-instantiated body
    /// rather than on the module as the pinned interpreter reads it.
    pub(crate) fn havoc_seeded_before(&self, position: usize) -> bool {
        self.havoc_seeds.iter().any(|seed| seed.position < position)
    }
}

/// Stable name of an instruction variant, for refusal messages.
pub(crate) fn inst_name(inst: &Inst) -> &'static str {
    match inst {
        Inst::BinOp { .. } => "BinOp",
        Inst::UnOp { .. } => "UnOp",
        Inst::Overflow { .. } => "Overflow",
        Inst::ICmp { .. } => "ICmp",
        Inst::FCmp { .. } => "FCmp",
        Inst::Cast { .. } => "Cast",
        Inst::BoxDeref { .. } => "BoxDeref",
        Inst::Load { .. } => "Load",
        Inst::Store { .. } => "Store",
        Inst::Alloca { .. } => "Alloca",
        Inst::HeapAlloc { .. } => "HeapAlloc",
        Inst::GEP { .. } => "GEP",
        Inst::PtrData { .. } => "PtrData",
        Inst::PtrMetadata { .. } => "PtrMetadata",
        Inst::PtrFromParts { .. } => "PtrFromParts",
        Inst::AtomicLoad { .. } => "AtomicLoad",
        Inst::AtomicStore { .. } => "AtomicStore",
        Inst::AtomicRMW { .. } => "AtomicRMW",
        Inst::CmpXchg { .. } => "CmpXchg",
        Inst::Fence { .. } => "Fence",
        Inst::Br { .. } => "Br",
        Inst::CondBr { .. } => "CondBr",
        Inst::Switch { .. } => "Switch",
        Inst::Call { .. } => "Call",
        Inst::CallIndirect { .. } => "CallIndirect",
        Inst::Return { .. } => "Return",
        Inst::MakeAggregate { .. } => "MakeAggregate",
        Inst::MakeClosure { .. } => "MakeClosure",
        Inst::ArraySplat { .. } => "ArraySplat",
        Inst::ExtractField { .. } => "ExtractField",
        Inst::InsertField { .. } => "InsertField",
        Inst::ExtractElement { .. } => "ExtractElement",
        Inst::InsertElement { .. } => "InsertElement",
        Inst::Const { .. } => "Const",
        Inst::NullPtr => "NullPtr",
        Inst::GlobalAddr { .. } => "GlobalAddr",
        Inst::Undef { .. } => "Undef",
        Inst::Assume { .. } => "Assume",
        Inst::Assert { .. } => "Assert",
        Inst::Unreachable => "Unreachable",
        Inst::Copy { .. } => "Copy",
        Inst::Select { .. } => "Select",
        Inst::SeqMapAddK { .. } => "SeqMapAddK",
        Inst::SeqMapNot { .. } => "SeqMapNot",
        Inst::SeqMap { .. } => "SeqMap",
        Inst::Borrow { .. } => "Borrow",
        Inst::BorrowMut { .. } => "BorrowMut",
        Inst::EndBorrow { .. } => "EndBorrow",
        Inst::Retain { .. } => "Retain",
        Inst::Release { .. } => "Release",
        Inst::IsUnique { .. } => "IsUnique",
        Inst::Dealloc { .. } => "Dealloc",
        Inst::MemCopy { .. } => "MemCopy",
        Inst::MemSet { .. } => "MemSet",
        Inst::Drop { .. } => "Drop",
        Inst::OpenFrame { .. } => "OpenFrame",
        Inst::BindSlot { .. } => "BindSlot",
        Inst::LoadSlot { .. } => "LoadSlot",
        Inst::CloseFrame { .. } => "CloseFrame",
        Inst::CoroSuspend { .. } => "CoroSuspend",
        Inst::Invoke { .. } => "Invoke",
        Inst::LandingPad { .. } => "LandingPad",
        Inst::Resume { .. } => "Resume",
        Inst::DialectOp(_) => "DialectOp",
        Inst::AssertInvoke { .. } => "AssertInvoke",
        Inst::CallCannotUnwind { .. } => "CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "CallIndirectCannotUnwind",
        Inst::DropInvoke { .. } => "DropInvoke",
        Inst::InvokeIndirect { .. } => "InvokeIndirect",
        Inst::TensorContract { .. } => "TensorContract",
        Inst::TensorMap { .. } => "TensorMap",
        Inst::TensorReduce { .. } => "TensorReduce",
        Inst::TensorView { .. } => "TensorView",
        Inst::TensorGather { .. } => "TensorGather",
        Inst::TensorScatter { .. } => "TensorScatter",
    }
}

fn index_u32(index: usize) -> u32 {
    u32::try_from(index).unwrap_or(u32::MAX)
}

fn control_flow(
    block: BlockId,
    inst_index: Option<usize>,
    detail: impl Into<String>,
) -> TrustIrBodyRefusal {
    TrustIrBodyRefusal::ControlFlow {
        block,
        inst_index: inst_index.map(index_u32),
        detail: detail.into(),
    }
}

fn malformed(detail: impl Into<String>) -> TrustIrBodyRefusal {
    TrustIrBodyRefusal::Malformed {
        detail: detail.into(),
    }
}

/// Where the instruction currently being checked sits.
#[derive(Clone, Copy)]
struct At {
    block: BlockId,
    index: usize,
}

impl At {
    fn unsupported(self, inst: &'static str, detail: impl Into<String>) -> TrustIrBodyRefusal {
        TrustIrBodyRefusal::UnsupportedInstruction {
            block: self.block,
            inst_index: index_u32(self.index),
            inst,
            detail: detail.into(),
        }
    }

    fn ill_typed(self, detail: impl Into<String>) -> TrustIrBodyRefusal {
        TrustIrBodyRefusal::IllTyped {
            block: self.block,
            inst_index: index_u32(self.index),
            detail: detail.into(),
        }
    }

    fn unsupported_type(self, ty: &Ty) -> TrustIrBodyRefusal {
        TrustIrBodyRefusal::UnsupportedType {
            block: Some(self.block),
            inst_index: Some(index_u32(self.index)),
            ty: ty.to_string(),
        }
    }

    fn scalar(self, ty: &Ty) -> Result<ScalarTy, TrustIrBodyRefusal> {
        ScalarTy::from_ty(ty).ok_or_else(|| self.unsupported_type(ty))
    }

    fn arity(self, node: &InstrNode, expected: usize) -> Result<(), TrustIrBodyRefusal> {
        if node.results.len() == expected {
            Ok(())
        } else {
            Err(self.ill_typed(format!(
                "{} declares {} results, v0 requires exactly {expected}",
                inst_name(&node.inst),
                node.results.len()
            )))
        }
    }
}

/// A value visible at the current chain position.
#[derive(Debug, Clone)]
enum Val {
    Scalar(ScalarTy),
    /// A compile-time scalar tuple, complete or built by `Undef` + `InsertField`.
    Static {
        ty: Ty,
        fields: Vec<ScalarTy>,
        set: Vec<Option<ValueId>>,
    },
}

type StaticAggregateState = (Ty, Vec<ScalarTy>, Vec<Option<ValueId>>);

#[derive(Default)]
struct Env {
    values: BTreeMap<ValueId, Val>,
    steps: Vec<Step>,
    value_types: BTreeMap<ValueId, ScalarTy>,
    havoc_seeds: Vec<HavocSeed>,
}

impl Env {
    fn define(&mut self, value: ValueId, val: Val) -> Result<(), TrustIrBodyRefusal> {
        if let Val::Scalar(ty) = &val {
            self.value_types.insert(value, *ty);
        }
        if self.values.insert(value, val).is_some() {
            return Err(malformed(format!(
                "SSA value %{} is defined more than once",
                value.0
            )));
        }
        Ok(())
    }

    fn operand(
        &self,
        at: At,
        value: ValueId,
        expected: ScalarTy,
    ) -> Result<(), TrustIrBodyRefusal> {
        match self.values.get(&value) {
            None => Err(malformed(format!(
                "bb{} inst {}: %{} is used before its definition in chain order (or never defined)",
                at.block.0, at.index, value.0
            ))),
            Some(Val::Static { .. }) => Err(at.ill_typed(format!(
                "%{} is an aggregate where a {} scalar is required",
                value.0,
                expected.to_ty()
            ))),
            Some(Val::Scalar(actual)) if *actual != expected => Err(at.ill_typed(format!(
                "%{} has type {}, the instruction requires {}",
                value.0,
                actual.to_ty(),
                expected.to_ty()
            ))),
            Some(Val::Scalar(_)) => Ok(()),
        }
    }

    fn def(
        &mut self,
        at: At,
        position: usize,
        value: ValueId,
        ty: ScalarTy,
        expr: DefExpr,
    ) -> Result<(), TrustIrBodyRefusal> {
        self.define(value, Val::Scalar(ty))?;
        self.steps.push(Step {
            position,
            block: at.block,
            inst_index: index_u32(at.index),
            kind: StepKind::Def { value, ty, expr },
        });
        Ok(())
    }

    fn static_aggregate(
        &self,
        at: At,
        inst: &'static str,
        value: ValueId,
    ) -> Result<StaticAggregateState, TrustIrBodyRefusal> {
        match self.values.get(&value) {
            Some(Val::Static { ty, fields, set }) => Ok((ty.clone(), fields.clone(), set.clone())),
            Some(Val::Scalar(_)) => Err(at.unsupported(
                inst,
                format!("%{} is a scalar, not a tracked static aggregate", value.0),
            )),
            None => Err(malformed(format!(
                "bb{} inst {}: %{} is used before its definition in chain order (or never defined)",
                at.block.0, at.index, value.0
            ))),
        }
    }
}

fn static_tuple_fields(ty: &Ty) -> Option<Vec<ScalarTy>> {
    match ty {
        Ty::Tuple(fields) if !fields.is_empty() => fields.iter().map(ScalarTy::from_ty).collect(),
        _ => None,
    }
}

/// The v0 arithmetic a `BinOp` denotes, `None` for every operator v0 refuses.
///
/// Only the shared IR's explicitly Bool-typed connectives are admitted here.
fn bool_kind(op: BinOp) -> Option<BoolKind> {
    match op {
        BinOp::BAnd => Some(BoolKind::And),
        BinOp::BOr => Some(BoolKind::Or),
        BinOp::BXor => Some(BoolKind::Xor),
        _ => None,
    }
}

/// Exhaustive with no wildcard on purpose: a `BinOp` trust-ir adds later must
/// fail to compile here and be classified by hand, never fall into `None` or
/// `Some` by default.
fn arith_kind(op: BinOp) -> Option<ArithKind> {
    match op {
        BinOp::Add => Some(ArithKind::Add),
        BinOp::Sub => Some(ArithKind::Sub),
        BinOp::Mul => Some(ArithKind::Mul),
        BinOp::UDiv
        | BinOp::SDiv
        | BinOp::URem
        | BinOp::SRem
        | BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax
        | BinOp::And
        | BinOp::Or
        | BinOp::Xor
        | BinOp::Shl
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::BAnd
        | BinOp::BOr
        | BinOp::BXor
        // Rotates and `copysign` (trust-ir WS3.20): not modeled by v0's
        // lowering, which only encodes wrapping Add/Sub/Mul.
        | BinOp::RotL
        | BinOp::RotR
        | BinOp::FCopySign => None,
    }
}

fn overflow_kind(op: OverflowOp) -> ArithKind {
    match op {
        OverflowOp::AddOverflow => ArithKind::Add,
        OverflowOp::SubOverflow => ArithKind::Sub,
        OverflowOp::MulOverflow => ArithKind::Mul,
    }
}

const fn icmp_is_ordered(op: ICmpOp) -> bool {
    !matches!(op, ICmpOp::Eq | ICmpOp::Ne)
}

/// Check `function` against the v0 shape and flatten it into chain order.
pub(crate) fn check_function(
    module: &Module,
    function: &Function,
) -> Result<CheckedBody, TrustIrBodyRefusal> {
    // The weight blob table (trust-ir wire v70) holds the bytes a
    // `Constant::TensorBlob` names by digest. v0 models no tensor and no blob,
    // so a module that carries one is refused whole, by the table's name,
    // before any body is read; whether this function cites a row does not
    // matter.
    if !module.blobs.is_empty() {
        return Err(TrustIrBodyRefusal::UnsupportedModuleTable {
            table: "Module.blobs",
            detail: format!(
                "the module carries {} weight blob row(s); v0 models no tensor weight, so a \
                 module carrying them is not decided",
                module.blobs.len()
            ),
        });
    }
    let sig = module.func_type(function.ty).ok_or_else(|| {
        malformed(format!(
            "function type functy.{} of function #{} is missing",
            function.ty.0, function.id.0
        ))
    })?;
    if sig.is_vararg {
        return Err(malformed("vararg function types are outside v0"));
    }

    let chain = check_control_flow(function)?;
    let blocks = function
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect::<BTreeMap<_, _>>();
    let entry = blocks[&function.entry];

    let mut env = Env::default();
    let params = check_entry_params(sig, entry, &mut env)?;
    for ty in &sig.returns {
        if ScalarTy::from_ty(ty).is_none() {
            return Err(TrustIrBodyRefusal::UnsupportedType {
                block: None,
                inst_index: None,
                ty: ty.to_string(),
            });
        }
    }

    let mut positions = BTreeMap::new();
    let mut position = 0usize;
    for block_id in &chain {
        let block = blocks[block_id];
        for (index, node) in block.body.iter().enumerate() {
            let at = At {
                block: block.id,
                index,
            };
            positions.insert((block.id, index_u32(index)), position);
            check_node(sig, &blocks, &mut env, at, position, node)?;
            position += 1;
        }
    }

    Ok(CheckedBody {
        params,
        steps: env.steps,
        chain,
        positions,
        value_types: env.value_types,
        havoc_seeds: env.havoc_seeds,
    })
}

fn check_entry_params(
    sig: &FuncTy,
    entry: &Block,
    env: &mut Env,
) -> Result<Vec<(ValueId, ScalarTy)>, TrustIrBodyRefusal> {
    if entry.params.len() != sig.params.len() {
        return Err(malformed(format!(
            "entry block bb{} has {} params, the function type has {}",
            entry.id.0,
            entry.params.len(),
            sig.params.len()
        )));
    }
    let mut params = Vec::with_capacity(entry.params.len());
    for ((value, ty), sig_ty) in entry.params.iter().zip(&sig.params) {
        if ty != sig_ty {
            return Err(malformed(format!(
                "entry param %{} has type {ty}, the function type says {sig_ty}",
                value.0
            )));
        }
        let scalar = ScalarTy::from_ty(ty).ok_or_else(|| TrustIrBodyRefusal::UnsupportedType {
            block: Some(entry.id),
            inst_index: None,
            ty: ty.to_string(),
        })?;
        env.define(*value, Val::Scalar(scalar))?;
        params.push((*value, scalar));
    }
    Ok(params)
}

/// Build the chain: the entry, then each unique `Br` successor, ending in the
/// single `Return`. Refuses every other CFG shape.
fn check_control_flow(function: &Function) -> Result<Vec<BlockId>, TrustIrBodyRefusal> {
    let mut blocks = BTreeMap::new();
    for block in &function.blocks {
        if blocks.insert(block.id, block).is_some() {
            return Err(malformed(format!(
                "block bb{} is declared more than once",
                block.id.0
            )));
        }
    }
    if !blocks.contains_key(&function.entry) {
        return Err(control_flow(function.entry, None, "entry block is missing"));
    }

    for block in &function.blocks {
        if block.body.is_empty() {
            return Err(control_flow(block.id, None, "block has no terminator"));
        }
        let last = block.body.len() - 1;
        for (index, node) in block.body.iter().enumerate() {
            let terminator = node.inst.is_terminator();
            if index < last && terminator {
                return Err(control_flow(
                    block.id,
                    Some(index),
                    format!(
                        "{} terminator appears before the end of the block",
                        inst_name(&node.inst)
                    ),
                ));
            }
            if index == last && !terminator {
                return Err(control_flow(
                    block.id,
                    Some(index),
                    format!(
                        "block ends in {}, which is not a terminator",
                        inst_name(&node.inst)
                    ),
                ));
            }
            if index == last && !matches!(node.inst, Inst::Br { .. } | Inst::Return { .. }) {
                return Err(control_flow(
                    block.id,
                    Some(index),
                    format!(
                        "{} terminator is outside the v0 unconditional chain",
                        inst_name(&node.inst)
                    ),
                ));
            }
        }
    }

    let mut predecessors: BTreeMap<BlockId, usize> = BTreeMap::new();
    for block in &function.blocks {
        let last = block.body.len() - 1;
        if let Inst::Br { target, .. } = &block.body[last].inst {
            if !blocks.contains_key(target) {
                return Err(control_flow(
                    block.id,
                    Some(last),
                    format!("Br targets missing block bb{}", target.0),
                ));
            }
            if *target == function.entry {
                return Err(control_flow(
                    block.id,
                    Some(last),
                    "Br targets the entry block (back edge)",
                ));
            }
            *predecessors.entry(*target).or_default() += 1;
        }
    }
    for (target, count) in &predecessors {
        if *count > 1 {
            return Err(control_flow(
                *target,
                None,
                format!("block has {count} predecessors; v0 admits exactly one"),
            ));
        }
    }
    for block in &function.blocks {
        if block.id != function.entry && !predecessors.contains_key(&block.id) {
            return Err(control_flow(
                block.id,
                None,
                "block has no predecessor (unreachable)",
            ));
        }
    }

    let mut chain = Vec::with_capacity(blocks.len());
    let mut visited = BTreeSet::new();
    let mut current = function.entry;
    loop {
        if !visited.insert(current) {
            return Err(control_flow(current, None, "Br closes a cycle (back edge)"));
        }
        chain.push(current);
        let block = blocks[&current];
        match &block.body[block.body.len() - 1].inst {
            Inst::Br { target, .. } => current = *target,
            _ => break,
        }
    }
    if let Some(unreached) = function
        .blocks
        .iter()
        .find(|block| !visited.contains(&block.id))
    {
        return Err(control_flow(
            unreached.id,
            None,
            "block is not reachable from the entry along the chain",
        ));
    }
    Ok(chain)
}

fn check_node(
    sig: &FuncTy,
    blocks: &BTreeMap<BlockId, &Block>,
    env: &mut Env,
    at: At,
    position: usize,
    node: &InstrNode,
) -> Result<(), TrustIrBodyRefusal> {
    match &node.inst {
        Inst::MakeClosure { .. } => Err(at.unsupported(
            "MakeClosure",
            "runtime closure construction and its ordered live captures are outside the scalar body lane",
        )),
        Inst::Const { ty, value } => {
            let scalar = at.scalar(ty)?;
            at.arity(node, 1)?;
            let expr = match (scalar, value) {
                (ScalarTy::Int { .. }, Constant::Int(k)) => {
                    let (min, max) = scalar.int_bounds().unwrap_or((0, -1));
                    if *k < min || *k > max {
                        return Err(at.ill_typed(format!(
                            "integer constant {k} is outside the range of {ty}; v0 refuses to rely on masking"
                        )));
                    }
                    DefExpr::IntConst(*k)
                }
                (ScalarTy::Bool, Constant::Bool(b)) => DefExpr::BoolConst(*b),
                // A trust-ir v50 `Splat` is the uniform ARRAY constant
                // `[elem; len]`. It inhabits only an array type, which
                // `at.scalar` has already refused above, so at a scalar type
                // it is ill-typed. Decided by name, not by the wildcard below,
                // and without reading `len`: constant size at every length.
                (ScalarTy::Int { .. }, Constant::Bool(_))
                | (ScalarTy::Bool, Constant::Int(_))
                | (_, Constant::U128(_))
                | (_, Constant::Splat { .. }) => {
                    return Err(at.ill_typed(format!("constant {value:?} does not inhabit {ty}")));
                }
                // A trust-ir v70 `TensorBlob` names a weight in the module
                // blob table by digest and shape. It inhabits only an integer
                // `Ty::Tensor`, which `at.scalar` has already refused above,
                // so at a scalar type it is ill-typed. Decided by name, without
                // reading the digest, the extents or the table.
                (_, Constant::TensorBlob { .. }) => {
                    return Err(at.ill_typed(format!(
                        "constant TensorBlob (a weight in the module blob table) does not \
                         inhabit {ty}; it inhabits only a tensor type, which v0 does not model"
                    )));
                }
                _ => {
                    return Err(at.unsupported(
                        "Const",
                        format!("constant {value:?} at {ty} is outside v0"),
                    ));
                }
            };
            env.def(at, position, node.results[0], scalar, expr)
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            if let Some(kind) = bool_kind(*op) {
                if at.scalar(ty)? != ScalarTy::Bool {
                    return Err(at.ill_typed(format!("BinOp::{op:?} requires scalar Bool")));
                }
                env.operand(at, *lhs, ScalarTy::Bool)?;
                env.operand(at, *rhs, ScalarTy::Bool)?;
                at.arity(node, 1)?;
                return env.def(
                    at,
                    position,
                    node.results[0],
                    ScalarTy::Bool,
                    DefExpr::BoolBinary {
                        op: kind,
                        lhs: *lhs,
                        rhs: *rhs,
                    },
                );
            }
            let Some(kind) = arith_kind(*op) else {
                return Err(at.unsupported("BinOp", format!("BinOp::{op:?} is outside v0")));
            };
            let scalar = at.scalar(ty)?;
            if scalar == ScalarTy::Bool {
                return Err(at.unsupported("BinOp", "arithmetic on Bool is outside v0"));
            }
            env.operand(at, *lhs, scalar)?;
            env.operand(at, *rhs, scalar)?;
            at.arity(node, 1)?;
            let expr = DefExpr::Wrap {
                op: kind,
                lhs: *lhs,
                rhs: *rhs,
            };
            env.def(at, position, node.results[0], scalar, expr)
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            let scalar = at.scalar(ty)?;
            if scalar == ScalarTy::Bool {
                return Err(at.unsupported("Overflow", "overflow arithmetic on Bool is outside v0"));
            }
            env.operand(at, *lhs, scalar)?;
            env.operand(at, *rhs, scalar)?;
            at.arity(node, 2)?;
            let kind = overflow_kind(*op);
            let value = DefExpr::Wrap {
                op: kind,
                lhs: *lhs,
                rhs: *rhs,
            };
            let flag = DefExpr::OverflowFlag {
                op: kind,
                operand_ty: scalar,
                lhs: *lhs,
                rhs: *rhs,
            };
            env.def(at, position, node.results[0], scalar, value)?;
            env.def(at, position, node.results[1], ScalarTy::Bool, flag)
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let scalar = at.scalar(ty)?;
            if scalar == ScalarTy::Bool && icmp_is_ordered(*op) {
                return Err(at.unsupported(
                    "ICmp",
                    format!("ordered ICmp::{op:?} on Bool is outside v0"),
                ));
            }
            env.operand(at, *lhs, scalar)?;
            env.operand(at, *rhs, scalar)?;
            at.arity(node, 1)?;
            let expr = DefExpr::ICmp {
                op: *op,
                operand_ty: scalar,
                lhs: *lhs,
                rhs: *rhs,
            };
            env.def(at, position, node.results[0], ScalarTy::Bool, expr)
        }
        Inst::Copy { ty, operand } => {
            if matches!(ty, Ty::Tuple(_)) {
                return Err(at.unsupported("Copy", "copy of an aggregate is outside v0"));
            }
            let scalar = at.scalar(ty)?;
            env.operand(at, *operand, scalar)?;
            at.arity(node, 1)?;
            env.def(
                at,
                position,
                node.results[0],
                scalar,
                DefExpr::Alias(*operand),
            )
        }
        Inst::MakeAggregate {
            ty,
            variant,
            fields: operands,
        } => {
            let Some(fields) = static_tuple_fields(ty) else {
                return Err(at.unsupported(
                    "MakeAggregate",
                    format!("MakeAggregate of {ty} is outside v0 (only a nonempty scalar tuple)"),
                ));
            };
            if variant.is_some() {
                return Err(at.ill_typed("a tuple MakeAggregate carries no variant index"));
            }
            if operands.len() != fields.len() {
                return Err(at.ill_typed(format!(
                    "MakeAggregate of {ty} has {} operands, expected {}",
                    operands.len(),
                    fields.len()
                )));
            }
            at.arity(node, 1)?;
            for (operand, field_ty) in operands.iter().zip(&fields) {
                env.operand(at, *operand, *field_ty)?;
            }
            // Shared IR defines tuple lanes in declaration order, with exact
            // types and no variant. Every lane aliases its original SSA value;
            // there is no havoc, layout reinterpretation or new solver term.
            env.define(
                node.results[0],
                Val::Static {
                    ty: ty.clone(),
                    fields,
                    set: operands.iter().copied().map(Some).collect(),
                },
            )
        }
        // Executing a TUPLE `Undef` is UNDEFINED BEHAVIOUR under the pinned
        // reference interpreter (trust-ir@4f09dab8 interpret.rs:1194 ->
        // `scalar_poison` :3476: a scalar `Undef` binds poison, a non-scalar
        // one is UB because aggregate poison is unmodelled; v0 admits only the
        // tuple form, below), so a body that
        // reaches one is not executable as written. v0 admits it only as a
        // FRESH UNCONSTRAINED HAVOC of the checked-op pack seed, which is the
        // over-approximation trust-ir's own `FreshSymbolicHavoc` doc sanctions
        // (proof/annotations.rs:168-178). That doc also imposes the condition
        // this arm must keep: nothing may narrow the fresh value. v0 keeps it
        // STRUCTURALLY rather than by trusting the annotation — every field
        // starts `None`, a read of a `None` field is refused below, and
        // `Env::operand` refuses a `Val::Static` wherever a scalar is
        // required, so no havoc value can ever reach a solver term, a `Br`
        // argument, a `Return`, or the interpreter replay. Admitting it is
        // recorded, because it changes which semantics the verdict is about.
        Inst::Undef { ty } => {
            let Some(fields) = static_tuple_fields(ty) else {
                return Err(at.unsupported(
                    "Undef",
                    format!("Undef of {ty} is outside v0 (only a tuple of admitted scalars)"),
                ));
            };
            at.arity(node, 1)?;
            let set = vec![None; fields.len()];
            env.havoc_seeds.push(HavocSeed {
                position,
                block: at.block,
                inst_index: index_u32(at.index),
                ty: ty.to_string(),
            });
            env.define(
                node.results[0],
                Val::Static {
                    ty: ty.clone(),
                    fields,
                    set,
                },
            )
        }
        Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => {
            let Some(fields) = static_tuple_fields(ty) else {
                return Err(at.unsupported(
                    "InsertField",
                    format!("InsertField into {ty} is outside v0"),
                ));
            };
            let (agg_ty, _, mut set) = env.static_aggregate(at, "InsertField", *aggregate)?;
            if &agg_ty != ty {
                return Err(at.ill_typed(format!(
                    "aggregate %{} has type {agg_ty}, the instruction says {ty}",
                    aggregate.0
                )));
            }
            let slot = *field as usize;
            let Some(field_ty) = fields.get(slot).copied() else {
                return Err(at.ill_typed(format!("field {field} is out of range for {ty}")));
            };
            env.operand(at, *value, field_ty)?;
            at.arity(node, 1)?;
            set[slot] = Some(*value);
            env.define(
                node.results[0],
                Val::Static {
                    ty: ty.clone(),
                    fields,
                    set,
                },
            )
        }
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } => {
            let (agg_ty, fields, set) = env.static_aggregate(at, "ExtractField", *aggregate)?;
            let slot = *field as usize;
            let Some(field_ty) = fields.get(slot).copied() else {
                return Err(at.ill_typed(format!("field {field} is out of range for {agg_ty}")));
            };
            let scalar = at.scalar(ty)?;
            if scalar != field_ty {
                return Err(at.ill_typed(format!(
                    "ExtractField says {ty}, field {field} of {agg_ty} is {}",
                    field_ty.to_ty()
                )));
            }
            let Some(source) = set[slot] else {
                // Reading a field no `InsertField` wrote would observe the
                // havoc seed. Refusing it is what keeps the havoc admission an
                // over-approximation: no verdict, and no replay, can ever
                // depend on a value the pinned interpreter calls undefined.
                return Err(at.unsupported(
                    "ExtractField",
                    format!(
                        "field {field} of %{} was never inserted, so reading it would observe the \
                         Undef havoc seed",
                        aggregate.0
                    ),
                ));
            };
            at.arity(node, 1)?;
            env.def(
                at,
                position,
                node.results[0],
                scalar,
                DefExpr::Alias(source),
            )
        }
        Inst::Assert {
            kind,
            site: Some(_),
            ..
        } => Err(at.unsupported(
            "Assert",
            format!(
                "a sited `{}` check is outside v0: its panic entry and location are not modelled",
                kind.keyword()
            ),
        )),
        Inst::Assert { kind, .. } if kind.operand_count() != 0 => Err(at.unsupported(
            "Assert",
            format!(
                "a `{}` check carries operands for its panic message, which v0 does not \
                 model",
                kind.keyword()
            ),
        )),
        Inst::Assume { cond } | Inst::Assert { cond, .. } => {
            env.operand(at, *cond, ScalarTy::Bool)?;
            at.arity(node, 0)?;
            let kind = if matches!(node.inst, Inst::Assume { .. }) {
                StepKind::Assume { cond: *cond }
            } else {
                StepKind::Assert { cond: *cond }
            };
            env.steps.push(Step {
                position,
                block: at.block,
                inst_index: index_u32(at.index),
                kind,
            });
            Ok(())
        }
        Inst::Br { target, args } => {
            at.arity(node, 0)?;
            let target_block = blocks[target];
            if args.len() != target_block.params.len() {
                return Err(at.ill_typed(format!(
                    "Br passes {} args, bb{} declares {} params",
                    args.len(),
                    target.0,
                    target_block.params.len()
                )));
            }
            for ((param, param_ty), arg) in target_block.params.iter().zip(args) {
                if matches!(param_ty, Ty::Tuple(_)) {
                    return Err(at.unsupported("Br", "aggregate block parameters are outside v0"));
                }
                let scalar = ScalarTy::from_ty(param_ty).ok_or_else(|| {
                    TrustIrBodyRefusal::UnsupportedType {
                        block: Some(*target),
                        inst_index: None,
                        ty: param_ty.to_string(),
                    }
                })?;
                env.operand(at, *arg, scalar)?;
                env.def(at, position, *param, scalar, DefExpr::Alias(*arg))?;
            }
            Ok(())
        }
        Inst::Return { values } => {
            at.arity(node, 0)?;
            if values.len() != sig.returns.len() {
                return Err(at.ill_typed(format!(
                    "Return carries {} values, the function type returns {}",
                    values.len(),
                    sig.returns.len()
                )));
            }
            for (value, ty) in values.iter().zip(&sig.returns) {
                let scalar = at.scalar(ty)?;
                env.operand(at, *value, scalar)?;
            }
            Ok(())
        }
        // Bulk memory writes (trust-ir WS3.20). v0 models no memory at all —
        // no pointers, no bytes, no provenance — so it cannot say what a body
        // that copies or fills memory computes, nor that the write is in
        // bounds. Refused BY NAME so the refusal says why; a verdict about
        // such a body could only be about some other program.
        Inst::MemCopy { overlap, .. } => Err(at.unsupported(
            "MemCopy",
            format!(
                "bulk {} is a memory effect; v0 models no memory, so a body containing it \
                 is not decided",
                if *overlap { "memmove" } else { "memcpy" }
            ),
        )),
        Inst::MemSet { .. } => Err(at.unsupported(
            "MemSet",
            "bulk memset is a memory effect; v0 models no memory, so a body containing it is \
             not decided",
        )),
        // A drop (trust-ir v47) runs the dropped type's destructor: it frees,
        // and it may run arbitrary user code. trust-ir's own executable models
        // both refuse it (no destructor model), and so does v0: reading it as a
        // no-op would decide a different program. Refused BY NAME.
        Inst::Drop { ty, .. } => Err(at.unsupported(
            "Drop",
            format!(
                "dropping a {ty} runs its destructor; v0 models no destructor and no memory, \
                 so a body containing it is not decided"
            ),
        )),
        // The tensor region (trust-ir v67-v69): contraction, elementwise map,
        // reduction, affine view, gather and scatter, each over `Ty::Tensor`
        // values. v0 models scalars and static tuples only; a tensor is a
        // run-time collection with no sort here, so none of its operations
        // can be decided. Refused BY NAME, before any operand, axis, node or
        // index is read, so the refusal is the same at every shape.
        Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => Err(at.unsupported(
            inst_name(&node.inst),
            "a tensor operation over run-time tensor values; v0 models scalars and static \
             tuples only, so a body containing it is not decided",
        )),
        Inst::BoxDeref { .. } => Err(at.unsupported(
            "BoxDeref",
            "Box pointee validity is not decided by v0; a named premise is not an established \
             validity fact and cannot authorize an unchecked scalar memory operation",
        )),
        // Every other instruction is outside v0. Listed rather than matched
        // by a wildcard, so an instruction trust-ir adds later fails to
        // compile HERE and is classified by hand instead of inheriting a
        // default.
        other @ (Inst::UnOp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        // trust-ir v50: `[value; n]`, the uniform array. Its result is an
        // ARRAY, and v0 models scalars and static tuples only, so like the
        // other array constructs it is outside v0. Refused by name without
        // reading `n`: the refusal costs the same at every length.
        | Inst::ArraySplat { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Unreachable
        | Inst::Select { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::DialectOp(_)
        | Inst::AssertInvoke { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::DropInvoke { .. }
        | Inst::InvokeIndirect { .. }) => Err(at.unsupported(inst_name(other), "instruction is outside v0")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `lower.rs` mints a `ScalarTy` at DOUBLE width to encode the overflow
    /// flag, so 64-bit operands produce `bits == 128`. That value is only ever
    /// handed to `lower::scalar_type`; if a future caller passes it here
    /// instead, it must narrow rather than overflow the shift or mint a
    /// silently wrong `Ty`.
    #[test]
    fn the_widened_scalar_type_narrows_instead_of_overflowing() {
        for signed in [false, true] {
            let widened = ScalarTy::Int { bits: 128, signed };
            assert_eq!(widened.int_bounds(), None);
            assert_eq!(widened.to_ty(), Ty::Error);
        }
        assert_eq!(ScalarTy::Bool.int_bounds(), None);
    }

    /// Every width `from_ty` admits round-trips, and its bounds are the type's.
    #[test]
    fn admitted_widths_round_trip_with_their_bounds() {
        for (ty, bounds) in [
            (Ty::U8, (0, 255)),
            (Ty::I8, (-128, 127)),
            (Ty::U16, (0, 65535)),
            (Ty::I16, (-32768, 32767)),
            (Ty::U32, (0, 4_294_967_295)),
            (Ty::I32, (-2_147_483_648, 2_147_483_647)),
            (Ty::U64, (0, u64::MAX as i128)),
            (Ty::I64, (i64::MIN as i128, i64::MAX as i128)),
        ] {
            let scalar = ScalarTy::from_ty(&ty).expect("admitted");
            assert_eq!(scalar.to_ty(), ty);
            assert_eq!(scalar.int_bounds(), Some(bounds));
        }
        assert_eq!(ScalarTy::from_ty(&Ty::Bool), Some(ScalarTy::Bool));
        assert_eq!(ScalarTy::from_ty(&Ty::U128), None);
        // Nominal function items have no modeled scalar payload. Distinct
        // definitions must never be reinterpreted as pointer-sized integers.
        for id in [0, 1] {
            assert_eq!(
                ScalarTy::from_ty(&Ty::FnItem(trust_ir::FuncId::new(id))),
                None
            );
        }
    }

    /// The layer BEHIND the wire-identity probe: while trust-ir's binary
    /// writer has no tag for `MemCopy`/`MemSet`, the digest refuses such a
    /// body first; once the tags land that probe goes quiet and this check is
    /// what refuses it. Measured directly so it cannot rot unseen meanwhile.
    /// A `Drop` (trust-ir v47) has a wire tag, so this check is the only
    /// thing that refuses it.
    #[test]
    fn memory_effects_are_refused_by_name() {
        let v = ValueId::new;
        for (name, inst) in [
            (
                "MemCopy",
                Inst::MemCopy {
                    dst: v(0),
                    src: v(1),
                    bytes: v(0),
                    overlap: false,
                },
            ),
            (
                "MemCopy",
                Inst::MemCopy {
                    dst: v(0),
                    src: v(1),
                    bytes: v(0),
                    overlap: true,
                },
            ),
            (
                "MemSet",
                Inst::MemSet {
                    dst: v(0),
                    byte: v(1),
                    bytes: v(0),
                },
            ),
            (
                "BoxDeref",
                Inst::BoxDeref {
                    ptr_ty: Ty::Ptr,
                    pointee: trust_ir::box_validity::BoxPointee::Sized { ty: Ty::U8 },
                    operand: v(0),
                    fact: Box::new(trust_ir::box_validity::BoxValidityFact::premise(
                        trust_ir::box_validity::BoxDerefSite {
                            item: [7; 16],
                            ordinal: 0,
                        },
                        trust_ir::box_validity::BoxFactSession::PROOF_SNAPSHOT,
                        trust_ir::box_validity::PremiseRoot::ParamByValue,
                    )),
                },
            ),
            // trust-ir v47: a drop runs a destructor; v0 models none.
            (
                "Drop",
                Inst::Drop {
                    ty: Ty::U8,
                    ptr: v(0),
                },
            ),
        ] {
            let module = one_instruction_module(InstrNode::new(inst));
            match check_function(&module, &module.functions[0]) {
                Err(TrustIrBodyRefusal::UnsupportedInstruction {
                    block,
                    inst_index,
                    inst,
                    detail,
                }) => {
                    assert_eq!(inst, name);
                    assert_eq!((block, inst_index), (BlockId::new(0), 0));
                    assert!(detail.contains("not decided"), "{name}: {detail}");
                }
                other => panic!("{name}: expected UnsupportedInstruction, got {other:?}"),
            }
        }
    }

    /// A trust-ir v49 unwritten aggregate lane (`Constant::Uninit`) is not a
    /// value v0 can read: in its only legal home, an aggregate constant, the
    /// type is outside v0, and a bare one at a scalar type is refused as an
    /// unsupported constant. Never decided either way.
    #[test]
    fn an_unwritten_lane_is_never_decided() {
        let lane = Ty::Tuple(vec![Ty::U8, Ty::U8]);
        for (label, ty, value) in [
            (
                "aggregate",
                lane,
                Constant::Aggregate(vec![Constant::Int(1), Constant::Uninit]),
            ),
            ("scalar", Ty::U8, Constant::Uninit),
        ] {
            let node =
                InstrNode::new(Inst::Const { ty, value }).with_results(vec![ValueId::new(2)]);
            let module = one_instruction_module(node);
            match check_function(&module, &module.functions[0]) {
                Err(TrustIrBodyRefusal::UnsupportedType { .. }) if label == "aggregate" => {}
                Err(TrustIrBodyRefusal::UnsupportedInstruction { inst, detail, .. })
                    if label == "scalar" =>
                {
                    assert_eq!(inst, "Const");
                    assert!(detail.contains("outside v0"), "{detail}");
                }
                other => panic!("{label}: expected a refusal, got {other:?}"),
            }
        }
    }

    /// trust-ir v50's constant-size uniform array `[v; n]` is never decided,
    /// in either spelling: the register `ArraySplat` is refused by name, a
    /// `Const` `Splat` at its array type is an unsupported type, and a `Splat`
    /// at a scalar type is ill-typed.
    ///
    /// The refusal must cost the same at every length. Nothing here times
    /// anything: the same refusal comes back at two copies and at `u64::MAX`
    /// copies, and a pass that walked `n` could not return at 2^64 elements.
    /// The test itself allocates nothing per element.
    #[test]
    fn a_uniform_array_is_never_decided_at_any_length() {
        let v = ValueId::new;
        let refusals = |len: u64| {
            let mut module = one_instruction_module(InstrNode::new(Inst::Unreachable));
            let elem = module
                .add_type(Ty::U8)
                .expect("Module::add_type: test fixture");
            let array = Ty::Array(elem, len);
            let splat = Constant::splat(Constant::Int(7), len);
            assert!(
                matches!(splat, Constant::Splat { len: n, .. } if n == len),
                "{len} copies are spelled as a splat"
            );
            [
                Inst::ArraySplat {
                    ty: array.clone(),
                    value: v(1),
                },
                Inst::Const {
                    ty: array.clone(),
                    value: splat.clone(),
                },
                Inst::Const {
                    ty: Ty::U8,
                    value: splat,
                },
            ]
            .map(|inst| {
                module.functions[0].blocks[0].body[0] =
                    InstrNode::new(inst).with_results(vec![v(2)]);
                check_function(&module, &module.functions[0])
                    .expect_err("a uniform array is never decided")
            })
            .map(|refusal| (refusal, array.to_string()))
        };
        let small = refusals(2);
        for len in [2, 1 << 40, u64::MAX] {
            let [(register, _), (typed, array), (scalar, _)] = refusals(len);
            assert!(array.ends_with(&format!(" x {len}]")), "{array}");
            // The register spelling's refusal does not mention the length, so
            // it is the SAME refusal at every length.
            assert_eq!(register, small[0].0, "len {len}");
            assert_eq!(
                register,
                TrustIrBodyRefusal::UnsupportedInstruction {
                    block: BlockId::new(0),
                    inst_index: 0,
                    inst: "ArraySplat",
                    detail: "instruction is outside v0".to_string(),
                }
            );
            // The constant spellings name the type or value, which carry the
            // length as one number; everything else is the same.
            assert_eq!(
                typed,
                TrustIrBodyRefusal::UnsupportedType {
                    block: Some(BlockId::new(0)),
                    inst_index: Some(0),
                    ty: array,
                },
                "len {len}"
            );
            match scalar {
                TrustIrBodyRefusal::IllTyped {
                    block,
                    inst_index,
                    detail,
                } => {
                    assert_eq!((block, inst_index), (BlockId::new(0), 0));
                    assert!(detail.contains("does not inhabit u8"), "{detail}");
                    assert!(detail.contains(&format!("len: {len}")), "{detail}");
                }
                other => panic!("len {len}: expected IllTyped, got {other:?}"),
            }
        }
    }

    /// The six tensor operations of trust-ir v67-v69, each spelled in
    /// trust-ir's own text grammar and parsed by trust-ir's own parser, so no
    /// fixture field is a guess about the producer's shape. Every operand id
    /// is 10 or above, so none is defined in the host body a test splices an
    /// operation into.
    fn tensor_operations() -> Vec<(&'static str, Inst)> {
        let text = "; TrustIr text format v1
module \"tensor_operations\"

functy.0 = (tensor<i32, 2>, tensor<i32, 2>, i32, usize) -> ()

fn @t(functy.0) {
bb0(%10: tensor<i32, 2>, %11: tensor<i32, 2>, %12: i32, %13: usize):
    %14 = tensor_contract tensor<i32, 2> %10, %11 batch [] contract [1:0]
    %15 = tensor_map tensor<i32, 2> (%10, %11, %12) { add i32 $0, $1; neg i32 $3 }
    %16 = tensor_reduce smax tensor<i32, 1> %10 axes [0] order row_major
    %17 = tensor_view tensor<i32, 2> %10 params [%13] exprs [coord(1), coord(0)] shape [$0, $1] index [$1, $0] fill %12
    %18 = tensor_gather tensor<i32, 1> %10 coords [%12, %13]
    %19 = tensor_scatter tensor<i32, 2> %10, %11 coords [%12, %13]
    ret
}
";
        let module = trust_ir::parser::parse_module(text).expect("trust-ir parses its own text");
        let names = [
            "TensorContract",
            "TensorMap",
            "TensorReduce",
            "TensorView",
            "TensorGather",
            "TensorScatter",
        ];
        let body = &module.functions[0].blocks[0].body;
        assert_eq!(body.len(), names.len() + 1, "six operations and a return");
        names
            .into_iter()
            .zip(body.iter().map(|node| node.inst.clone()))
            .collect()
    }

    /// Each tensor operation is its own variant, so a refusal that names it
    /// is about that operation and no other.
    fn is_variant(name: &str, inst: &Inst) -> bool {
        match name {
            "TensorContract" => matches!(inst, Inst::TensorContract { .. }),
            "TensorMap" => matches!(inst, Inst::TensorMap { .. }),
            "TensorReduce" => matches!(inst, Inst::TensorReduce { .. }),
            "TensorView" => matches!(inst, Inst::TensorView { .. }),
            "TensorGather" => matches!(inst, Inst::TensorGather { .. }),
            "TensorScatter" => matches!(inst, Inst::TensorScatter { .. }),
            _ => false,
        }
    }

    /// trust-ir v67-v69's tensor operations are refused BY NAME, by
    /// `inst_name` and by the body checker, before any operand is read: no
    /// operand here is defined in the host body, and the refusal is still the
    /// named one.
    #[test]
    fn every_tensor_operation_is_refused_by_name() {
        let operations = tensor_operations();
        assert_eq!(operations.len(), 6);
        for (name, inst) in operations {
            assert!(is_variant(name, &inst), "{name}: parsed {inst:?}");
            assert_eq!(inst_name(&inst), name);
            let node = InstrNode::new(inst).with_results(vec![ValueId::new(2)]);
            let module = one_instruction_module(node);
            assert_eq!(
                check_function(&module, &module.functions[0]),
                Err(TrustIrBodyRefusal::UnsupportedInstruction {
                    block: BlockId::new(0),
                    inst_index: 0,
                    inst: name,
                    detail: "a tensor operation over run-time tensor values; v0 models scalars \
                             and static tuples only, so a body containing it is not decided"
                        .to_string(),
                }),
                "{name}"
            );
        }
    }

    /// A `Ty::Tensor` (trust-ir v67) has no scalar reading, so it is refused
    /// as an unsupported type, spelled `tensor<..>`, wherever it appears: an
    /// entry parameter, a return, the type of a `Const`.
    #[test]
    fn a_tensor_type_is_refused_wherever_it_appears() {
        let tensor = Ty::Tensor(Box::new(Ty::I32), 2);
        let spelled = tensor.to_string();
        assert_eq!(spelled, "tensor<i32, 2>");

        let twin = one_instruction_module(admitted_const());
        assert!(check_function(&twin, &twin.functions[0]).is_ok());

        let mut param = one_instruction_module(admitted_const());
        param.func_types[0].params[1] = tensor.clone();
        param.functions[0].blocks[0].params[1].1 = tensor.clone();
        assert_eq!(
            check_function(&param, &param.functions[0]),
            Err(TrustIrBodyRefusal::UnsupportedType {
                block: Some(BlockId::new(0)),
                inst_index: None,
                ty: spelled.clone(),
            })
        );

        let mut ret = one_instruction_module(admitted_const());
        ret.func_types[0].returns = vec![tensor.clone()];
        assert_eq!(
            check_function(&ret, &ret.functions[0]),
            Err(TrustIrBodyRefusal::UnsupportedType {
                block: None,
                inst_index: None,
                ty: spelled.clone(),
            })
        );

        let digest = Module::new("scratch").intern_blob(vec![0; 16]);
        let node = InstrNode::new(Inst::Const {
            ty: tensor,
            value: Constant::TensorBlob {
                digest,
                dims: vec![2, 2],
            },
        })
        .with_results(vec![ValueId::new(2)]);
        let constant = one_instruction_module(node);
        assert_eq!(
            check_function(&constant, &constant.functions[0]),
            Err(TrustIrBodyRefusal::UnsupportedType {
                block: Some(BlockId::new(0)),
                inst_index: Some(0),
                ty: spelled,
            })
        );
    }

    /// A trust-ir v70 `TensorBlob` at a scalar type is ill-typed and refused
    /// BY NAME. Its twin, an in-range integer at the same type, is admitted.
    #[test]
    fn a_tensor_blob_constant_is_refused_by_name() {
        let digest = Module::new("scratch").intern_blob(vec![7; 8]);
        let blob = |value| {
            InstrNode::new(Inst::Const { ty: Ty::U64, value }).with_results(vec![ValueId::new(2)])
        };
        let refused = one_instruction_module(blob(Constant::TensorBlob {
            digest,
            dims: vec![1],
        }));
        match check_function(&refused, &refused.functions[0]) {
            Err(TrustIrBodyRefusal::IllTyped {
                block,
                inst_index,
                detail,
            }) => {
                assert_eq!((block, inst_index), (BlockId::new(0), 0));
                assert!(detail.starts_with("constant TensorBlob "), "{detail}");
                assert!(detail.contains("does not inhabit u64"), "{detail}");
            }
            other => panic!("expected IllTyped naming TensorBlob, got {other:?}"),
        }
        let admitted = one_instruction_module(blob(Constant::Int(7)));
        assert!(check_function(&admitted, &admitted.functions[0]).is_ok());
    }

    /// A module carrying a weight blob table (`Module.blobs`, trust-ir v70) is
    /// refused whole, by the table's name, even when the checked body is
    /// admitted and cites no row. The twin differs by the one interned blob.
    #[test]
    fn a_module_carrying_blobs_is_refused_by_the_table_name() {
        let twin = one_instruction_module(admitted_const());
        assert!(check_function(&twin, &twin.functions[0]).is_ok());

        let mut carrying = one_instruction_module(admitted_const());
        carrying.intern_blob(vec![1, 2, 3, 4]);
        assert_eq!(
            check_function(&carrying, &carrying.functions[0]),
            Err(TrustIrBodyRefusal::UnsupportedModuleTable {
                table: "Module.blobs",
                detail: "the module carries 1 weight blob row(s); v0 models no tensor weight, so \
                         a module carrying them is not decided"
                    .to_string(),
            })
        );
    }

    /// `%2 = const u8 1`, a node v0 admits.
    fn admitted_const() -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::U8,
            value: Constant::Int(1),
        })
        .with_results(vec![ValueId::new(2)])
    }

    /// `fn one(u64, u8) { <node>; return }`.
    fn one_instruction_module(node: InstrNode) -> Module {
        let v = ValueId::new;
        let mut module = Module::new("one");
        module.func_types.push(FuncTy {
            params: vec![Ty::U64, Ty::U8],
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        });
        let mut entry = Block::new(BlockId::new(0))
            .with_param(v(0), Ty::U64)
            .with_param(v(1), Ty::U8);
        entry.body = vec![node, InstrNode::new(Inst::Return { values: Vec::new() })];
        module.functions.push(Function {
            id: trust_ir::FuncId::new(0),
            name: "one".to_string(),
            ty: trust_ir::FuncTyId::new(0),
            entry: entry.id,
            blocks: vec![entry],
            proofs: Vec::new(),
            calling_conv: trust_ir::CallingConv::default(),
            linkage: trust_ir::Linkage::default(),
            attrs: trust_ir::FuncAttrs::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
            body_gate: None,
            display_path: None,
            section: None,
            visibility: trust_ir::Visibility::default(),
            retained: false,
        });
        module
    }
}
