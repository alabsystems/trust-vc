// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Merge bundle data types: VarDecl, TypedExpr, SortMeta, and related structs.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VarDecl {
    name: String,
    sort: SortMeta,
}

impl VarDecl {
    #[must_use]
    pub fn new(name: impl Into<String>, sort: SortMeta) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub fn sort(&self) -> &SortMeta {
        &self.sort
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypedExpr {
    expr: String,
    sort: SortMeta,
}

impl TypedExpr {
    #[must_use]
    pub fn new(expr: impl Into<String>, sort: SortMeta) -> Self {
        Self {
            expr: expr.into(),
            sort,
        }
    }

    #[must_use]
    pub fn expr(&self) -> &str {
        &self.expr
    }

    #[must_use]
    pub fn sort(&self) -> &SortMeta {
        &self.sort
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecreasesClause {
    obligation_id: String,
    measures: Vec<TypedExpr>,
}

impl DecreasesClause {
    #[must_use]
    pub fn new(obligation_id: impl Into<String>, measures: Vec<TypedExpr>) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            measures,
        }
    }

    #[must_use]
    pub fn obligation_id(&self) -> &str {
        &self.obligation_id
    }

    #[must_use]
    pub fn measures(&self) -> &[TypedExpr] {
        &self.measures
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TriggerGroup {
    obligation_id: String,
    patterns: Vec<TypedExpr>,
}

impl TriggerGroup {
    #[must_use]
    pub fn new(obligation_id: impl Into<String>, patterns: Vec<TypedExpr>) -> Self {
        Self {
            obligation_id: obligation_id.into(),
            patterns,
        }
    }

    #[must_use]
    pub fn obligation_id(&self) -> &str {
        &self.obligation_id
    }

    #[must_use]
    pub fn patterns(&self) -> &[TypedExpr] {
        &self.patterns
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
#[non_exhaustive]
pub enum SortMeta {
    Bool,
    BitVector {
        width: u32,
        signed: bool,
    },
    MathInt,
    Real,
    Opaque {
        name: String,
    },
    Seq {
        elem: Box<SortMeta>,
    },
    Set {
        elem: Box<SortMeta>,
    },
    Map {
        key: Box<SortMeta>,
        value: Box<SortMeta>,
    },
    FloatingPoint {
        exponent_bits: u32,
        significand_bits: u32,
    },
    Array {
        index: Box<SortMeta>,
        element: Box<SortMeta>,
    },
}

/// Declaration of an uninterpreted function symbol.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuncDeclMeta {
    /// Function symbol name (e.g., "factorial", "sum").
    name: String,
    /// Parameter names (positional, for trigger construction).
    param_names: Vec<String>,
    /// Parameter sorts.
    param_sorts: Vec<SortMeta>,
    /// Return sort.
    return_sort: SortMeta,
    /// Whether this function has recursive calls in its body.
    is_recursive: bool,
}

impl FuncDeclMeta {
    #[must_use]
    pub fn new(
        name: impl Into<String>,
        param_names: Vec<String>,
        param_sorts: Vec<SortMeta>,
        return_sort: SortMeta,
    ) -> Self {
        Self {
            name: name.into(),
            param_names,
            param_sorts,
            return_sort,
            is_recursive: false,
        }
    }

    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub fn param_names(&self) -> &[String] {
        &self.param_names
    }

    #[must_use]
    pub fn param_sorts(&self) -> &[SortMeta] {
        &self.param_sorts
    }

    #[must_use]
    pub fn return_sort(&self) -> &SortMeta {
        &self.return_sort
    }

    #[must_use]
    pub fn is_recursive(&self) -> bool {
        self.is_recursive
    }

    #[must_use]
    pub fn with_recursive(mut self, is_recursive: bool) -> Self {
        self.is_recursive = is_recursive;
        self
    }
}

/// Defining axiom for a (possibly recursive) function.
///
/// Encodes: `forall vars. {trigger} lhs == rhs`
/// where `lhs` is typically `f(a, b)` and `rhs` is the function body.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuelAxiomMeta {
    /// The function this axiom defines.
    function_name: String,
    /// Universally quantified bound variables with sorts.
    bound_vars: Vec<VarDecl>,
    /// The equality axiom as an SMT-LIB2 term: `(= (f a b) <body>)`.
    axiom_expr: TypedExpr,
    /// Trigger pattern (typically the function application `(f a b)`).
    trigger_pattern: TypedExpr,
}

impl FuelAxiomMeta {
    #[must_use]
    pub fn new(
        function_name: impl Into<String>,
        bound_vars: Vec<VarDecl>,
        axiom_expr: TypedExpr,
        trigger_pattern: TypedExpr,
    ) -> Self {
        Self {
            function_name: function_name.into(),
            bound_vars,
            axiom_expr,
            trigger_pattern,
        }
    }

    #[must_use]
    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    #[must_use]
    pub fn bound_vars(&self) -> &[VarDecl] {
        &self.bound_vars
    }

    #[must_use]
    pub fn axiom_expr(&self) -> &TypedExpr {
        &self.axiom_expr
    }

    #[must_use]
    pub fn trigger_pattern(&self) -> &TypedExpr {
        &self.trigger_pattern
    }
}

/// Auto-applied quantified lemma (broadcast).
///
/// Encodes: `forall vars. {triggers} [guard ==>] body`
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BroadcastLemmaMeta {
    /// Lemma name (e.g., "broadcast_lemma_sum_nonneg").
    name: String,
    /// Universally quantified bound variables with sorts.
    bound_vars: Vec<VarDecl>,
    /// The ensures body as an SMT-LIB2 term.
    body_expr: TypedExpr,
    /// Optional requires guard. If present, the axiom is `guard ==> body`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    guard_expr: Option<TypedExpr>,
    /// Trigger groups. Each inner Vec is a multi-trigger (AND).
    /// Outer Vec is alternative triggers (OR).
    trigger_groups: Vec<Vec<TypedExpr>>,
    /// Optional broadcast group for `broadcast_use!` scoping.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    group: Option<String>,
}

impl BroadcastLemmaMeta {
    #[must_use]
    pub fn new(
        name: impl Into<String>,
        bound_vars: Vec<VarDecl>,
        body_expr: TypedExpr,
        trigger_groups: Vec<Vec<TypedExpr>>,
    ) -> Self {
        Self {
            name: name.into(),
            bound_vars,
            body_expr,
            guard_expr: None,
            trigger_groups,
            group: None,
        }
    }

    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub fn bound_vars(&self) -> &[VarDecl] {
        &self.bound_vars
    }

    #[must_use]
    pub fn body_expr(&self) -> &TypedExpr {
        &self.body_expr
    }

    #[must_use]
    pub fn guard_expr(&self) -> Option<&TypedExpr> {
        self.guard_expr.as_ref()
    }

    #[must_use]
    pub fn trigger_groups(&self) -> &[Vec<TypedExpr>] {
        &self.trigger_groups
    }

    #[must_use]
    pub fn group(&self) -> Option<&str> {
        self.group.as_deref()
    }

    #[must_use]
    pub fn with_guard_expr(mut self, guard_expr: TypedExpr) -> Self {
        self.guard_expr = Some(guard_expr);
        self
    }

    #[must_use]
    pub fn with_group(mut self, group: impl Into<String>) -> Self {
        self.group = Some(group.into());
        self
    }
}
