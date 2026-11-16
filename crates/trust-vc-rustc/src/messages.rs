//! Verus's diagnostic texts, and the order in which Verus reports them.
//!
//! The harness compares messages and span labels by substring, so every
//! string here is copied from upstream Verus at the pinned revision (the
//! source location is given on each constant) and checked against the
//! reference run of upstream `basic.rs` with Verus and z3.

/// Which of Verus's checking phases produces an error.
///
/// Verus stops after the first phase that reports anything: errors found
/// while building VIR (`rust_to_vir*`) suppress the well-formedness check,
/// which suppresses the mode check, and so on. A crate that has errors from
/// two phases must only show the earlier phase's errors, or the harness's
/// error counts differ from Verus's. Building VIR reports an error per item;
/// every later phase stops at its first error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Phase {
    /// Building VIR from HIR: unsupported features, attribute errors, spec
    /// `==` type errors, `mut` parameters of spec functions, header rules.
    RustToVir,
    /// `vir/src/well_formed.rs`, `check_crate`, before it checks each
    /// function: the links between spec functions and their
    /// `decreases_by` functions.
    WellFormedCrate,
    /// `vir/src/well_formed.rs`: visibility of what a public specification
    /// refers to, datatype access, reveal targets.
    WellFormed,
    /// `vir/src/modes.rs`.
    Modes,
    /// `vir/src/ast_simplify.rs` (runs after lifetime checking).
    Simplify,
    /// `vir/src/ast_to_sst.rs`, run per module just before that module is
    /// verified.
    Sst,
    /// `vir/src/sst_elaborate.rs`: infer triggers after constructing all of
    /// the module's SST functions. Construction errors precede this stage,
    /// including errors in functions later than the rejected binder.
    SstElaboration,
}

impl Phase {
    /// Both stages belong to the same per-module SST boundary, after erase.
    pub const fn is_sst(self) -> bool {
        matches!(self, Self::Sst | Self::SstElaboration)
    }
}

/// `rust_verify/src/util.rs`, `unsupported_err!`: the prefix of every error
/// for a Rust feature Verus does not support.
pub const UNSUPPORTED_PREFIX: &str =
    "The verifier does not yet support the following Rust feature: ";

/// The message for an unsupported Rust feature.
#[must_use]
pub fn unsupported(feature: &str) -> String {
    format!("{UNSUPPORTED_PREFIX}{feature}")
}

/// `rust_to_vir_expr.rs`, `binopkind_to_binaryop_inner`: the feature named
/// for `&` (and `&=`) on two bools, reported at the left operand.
pub const BOOL_BITAND_FEATURE: &str =
    "bitwise AND for bools (i.e., the not-short-circuited version)";

/// See [`BOOL_BITAND_FEATURE`]: `|` (and `|=`) on two bools.
pub const BOOL_BITOR_FEATURE: &str = "bitwise OR for bools (i.e., the not-short-circuited version)";

/// `rust_verify/src/external.rs`, `VisitMod::visit_general`:
/// `#[verifier::external_body]` on an item other than a function, a
/// datatype or a constant, at the item.
pub const EXTERNAL_BODY_ITEM: &str = "#[verifier::external_body] doesn't make sense for this item type -- it is only applicable to functions and datatype declarations";

/// `rust_verify/src/util.rs`, `no_builtin_err`: a crate that never loads
/// `verus_builtin`, reported at the crate's span.
pub const NO_BUILTIN: &str = "Error: The verus_builtin crate was not imported. This is usually imported via `vstd`, and it is necessary to run Verus.";

/// Help attached to [`NO_BUILTIN`].
pub const NO_BUILTIN_HELP: &str =
    "For getting started with Verus, see: https://verus-lang.github.io/verus/guide/getting_started.html";

/// `fn_call_to_vir.rs`, `SpecEq`: operands of spec `==` whose types differ.
pub const SPEC_EQ_TYPES: &str = "mismatched types; types must be compatible to use == or !=";

/// Help attached to [`SPEC_EQ_TYPES`].
pub const SPEC_EQ_TYPES_HELP: &str =
    "decorations (like &,Ghost,Tracked,Box,Rc,...) are transparent for == or != in spec code";

/// Label on each operand of a [`SPEC_EQ_TYPES`] error.
#[must_use]
pub fn spec_eq_type_label(ty: &str) -> String {
    format!("this is `{ty}`")
}

/// `fn_call_to_vir.rs`, `SpecEq`: a `&mut` operand of spec `==` (without
/// `-V new-mut-ref`).
pub const SPEC_EQ_MUT_REF: &str =
    "Dereference this mutable reference to compare the value via Verus spec equality.";

/// `rust_to_vir_func.rs`, `check_item_fn`: a spec function with a `&mut`
/// parameter (without `-V new-mut-ref`).
pub const MUT_REF_PARAM_SPEC_FN: &str = "&mut parameter not allowed for spec functions";

/// `rust_to_vir_expr.rs`, `check_lit_int`: an integer literal outside its
/// type; `range` is VIR's `IntRange` in `Debug` form (`U(8)`, `I(128)`).
#[must_use]
pub fn lit_out_of_range(range: &str) -> String {
    format!("integer literal out of range {range}")
}

/// `rust_verify/src/reveal_hide.rs`, `handle_reveal_hide`: a fuel that is
/// not an unsuffixed integer literal that fits in `u32`, reported at the
/// reveal.
pub const FUEL_NOT_U32: &str = "Fuel must be a u32 value";

/// `vir/src/well_formed.rs`: an `assume` under `--no-cheating`.
pub const NO_CHEATING_ASSUME: &str = "assume/admit not allowed with --no-cheating";

/// `vir/src/well_formed.rs`: an `external_body` function under
/// `--no-cheating`.
pub const NO_CHEATING_EXTERNAL_BODY: &str =
    "external_body/assume_specification not allowed with --no-cheating";

/// Function header rules checked while Verus builds VIR
/// (`rust_to_vir_func.rs`, `check_item_fn`), all reported at the function's
/// signature, in this order.
pub mod header {
    /// A spec function with `requires` or `ensures`.
    pub const SPEC_REQUIRES_ENSURES: &str = "spec functions cannot have requires/ensures";
    /// `returns` is an exec/proof contract, never a spec definition.
    pub const SPEC_RETURNS: &str = "spec functions cannot have `returns` clause";
    /// The pure entry-state value has the actual function result type.
    pub const RETURNS_TYPE: &str =
        "type of `returns` clause does not match function return type";
    /// A returns marker has exactly one semantic expression.
    pub const RETURNS_COUNT: &str = "`returns` clause should have exactly 1 expression";
    /// A proof or exec function with `recommends`.
    pub const NON_SPEC_RECOMMENDS: &str = "non-spec functions cannot have recommends";
    /// `ensures` on a function whose written return type has no name.
    pub const UNNAMED_RETURN: &str =
        "the return value must be named in a function with an ensures clause";
    /// A named return value on a function with no written return type.
    pub const NAMED_DEFAULT_RETURN: &str =
        "unexpected named return value for function with default return";

    /// `vir/src/headers.rs`, `read_header_block`: a second `requires` call
    /// in one header, at that call.
    pub const SECOND_REQUIRES: &str =
        "only one call to requires allowed (use requires([e1, ..., en]) for multiple expressions";
    /// A second `recommends` call.
    pub const SECOND_RECOMMENDS: &str = "only one call to recommends allowed (use recommends([e1, ..., en]) for multiple expressions";
    /// A second `ensures` call.
    pub const SECOND_ENSURES: &str =
        "only one call to ensures allowed (use ensures([e1, ..., en]) for multiple expressions";
    /// A second returns marker, including one written in the function body.
    pub const SECOND_RETURNS: &str = "only one call to returns allowed";
    /// A second invariant mask spec (`opens_invariants ..`).
    pub const SECOND_MASK: &str = "only one invariant mask spec allowed";
    /// A second unwind spec (`no_unwind ..`).
    pub const SECOND_UNWIND: &str = "only one unwind spec allowed";

    /// The rejection of a second call of `item`'s header kind, for the
    /// header items the reader reads.
    #[must_use]
    pub fn second_call(item: crate::verus_items::VerusItem) -> Option<&'static str> {
        use crate::verus_items::VerusItem as V;
        match item {
            V::Requires => Some(SECOND_REQUIRES),
            V::Recommends => Some(SECOND_RECOMMENDS),
            V::Ensures => Some(SECOND_ENSURES),
            V::Returns => Some(SECOND_RETURNS),
            V::OpensInvariantsNone => Some(SECOND_MASK),
            V::NoUnwind | V::NoUnwindWhen => Some(SECOND_UNWIND),
            _ => None,
        }
    }
}

/// Body visibility and opacity rules (`rust_to_vir_func.rs`,
/// `get_body_visibility_and_fuel`), reported at the function's signature,
/// after the [`header`] rules.
pub mod publish {
    /// `open` on a proof or exec function.
    pub const OPEN_NOT_SPEC: &str = "function is marked `open` but it is not a `spec` function";
    /// `closed` on a proof or exec function.
    pub const CLOSED_NOT_SPEC: &str = "function is marked `closed` but it is not a `spec` function";
    /// `#[verifier::opaque]` on a proof or exec function.
    pub const OPAQUE_NOT_SPEC: &str = "function is marked `opaque` but it is not a `spec` function";
    /// `#[verifier::opaque]` on a spec function without a body.
    pub const OPAQUE_WITHOUT_BODY: &str = "opaque has no effect on a function without a body";
    /// `uninterp` on a function written with a body.
    pub const UNINTERP_WITH_BODY: &str = "function is marked `uninterp` but it has a body";
    /// `open` on a private function.
    pub const OPEN_NOT_PUB: &str = "function is marked `open` but not marked `pub`; for the body of a function to be visible, the function symbol must also be visible";
}

/// Well-formedness rules (`vir/src/well_formed.rs`).
pub mod wf {
    /// `check_function`: a function named `main`, anywhere, that is not exec.
    pub const MAIN_NOT_EXEC: &str = "`main` function should be #[verifier::exec]";

    /// Where a specification must be well formed wider than its function's
    /// module: the `disallow_private_access` reasons of `check_function`.
    /// `recommends` of a spec function are its `requires` there.
    pub const REASON_REQUIRES: &str = "'requires' clause of public function";
    /// See [`REASON_REQUIRES`].
    pub const REASON_ENSURES: &str = "'ensures' clause of public function";
    /// See [`REASON_REQUIRES`].
    pub const REASON_OPEN_SPEC: &str = "pub open spec function";
    /// See [`REASON_REQUIRES`].
    pub const REASON_DECREASES: &str = "'decreases' clause of public function";
    /// See [`REASON_REQUIRES`].
    pub const REASON_WHEN: &str = "'when' clause of public function";

    /// `check_path_and_get_function`: a reference to an item less visible
    /// than the area it appears in. `kind` is `function` or `const`.
    #[must_use]
    pub fn private_reference(reason: &str, kind: &str) -> String {
        format!("in {reason}, cannot refer to private {kind}")
    }

    /// `check_datatype_access`: a field expression or constructor of a
    /// datatype whose name is not visible throughout the required area.
    /// Message, primary label.
    #[must_use]
    pub fn non_visible_datatype(access: &str) -> (String, String) {
        (
            format!("disallowed: {access} for a non-visible datatype"),
            format!("this {access} is disallowed because of non-visibility"),
        )
    }

    /// Label at the datatype for [`non_visible_datatype`].
    #[must_use]
    pub fn only_visible_to(module: &str) -> String {
        format!("this datatype is only visible to `{module}`")
    }

    /// `check_datatype_access`: a field expression or constructor of a
    /// datatype whose fields are not all visible throughout the required
    /// area. Message, primary label.
    #[must_use]
    pub fn opaque_datatype(access: &str) -> (String, String) {
        (
            format!("disallowed: {access} for an opaque datatype"),
            format!("this {access} is disallowed because of datatype opaqueness"),
        )
    }

    /// Label at the datatype for [`opaque_datatype`].
    #[must_use]
    pub fn opaque_outside(module: &str) -> String {
        format!(
            "Verus treats this datatype as 'opaque' outside `{module}` (note that Verus always considers the most restrictive field for determining this)"
        )
    }

    /// Help of a datatype access error in an area with a reason:
    /// `required` is where the access must be well formed ("everywhere",
    /// "everywhere in the crate `c`", "everywhere in the module `c::m`").
    #[must_use]
    pub fn access_help(reason: &str, access: &str, required: &str, module: &str) -> String {
        format!(
            "note that because this is a {reason}, this {access} must be well-formed {required}, which is wider than `{module}`"
        )
    }

    /// `check_one_expr`, `ExprX::Fuel`: a reveal of a function whose body is
    /// not visible where the reveal is.
    #[must_use]
    pub fn reveal_closed(function: &str) -> String {
        format!(
            "reveal/fuel statement is not allowed here because the function `{function}` is marked 'closed' and thus its body is not visible here. (Note: 'reveal' statements are intended for functions that are opaque, not functions that are closed)"
        )
    }

    /// `check_one_expr`, `ExprX::Fuel`: `reveal_with_fuel` of a function
    /// without a `decreases` clause.
    pub const REVEAL_WITH_FUEL_NO_DECREASES: &str =
        "reveal_with_fuel statements require a spec function with a decreases clause";

    /// `check_one_expr`, `ExprX::Fuel`: a reveal of a proof or exec function.
    #[must_use]
    pub fn reveal_not_spec(mode: &str) -> String {
        format!("reveal/fuel statements require a spec-mode function, got {mode}-mode function")
    }

    /// `check_one_expr`, `ExprX::Fuel` of a `broadcast use`: its target is
    /// not a broadcast proof function (or a broadcast group).
    pub const BROADCAST_USE_NOT_BROADCAST: &str =
        "`broadcast use` statements require a broadcast proof fn";

    /// `check_one_expr`, `ExprX::Header`: a function header (`hide`, which
    /// is also `reveal_with_fuel(f, 0)`) left in the body because it is not
    /// among the body's leading statements.
    pub const HIDE_NOT_AT_START: &str = "This verus_builtin header should go at the beginning of the function body (this is probably a Verus bug, unless you are manually writing calls to Verus builtin headers, which is unusual)";
}

/// `vir/src/modes.rs`, `StmtX::Decl`: a `let` whose mode is not allowed where
/// it stands, such as `let tracked` in spec code.
#[must_use]
pub fn pattern_mode(mode: &str) -> String {
    format!("pattern cannot have mode {mode}")
}

/// The mode checker's messages (`vir/src/modes.rs`), each at the span the
/// checker reports it.
pub mod modes {
    /// `check_expr_has_mode`: an expression whose mode is above the mode
    /// its position needs (a function body, an argument, an assigned value,
    /// a returned value, a `let` initializer).
    #[must_use]
    pub fn expr_mode(found: &str, expected: &str) -> String {
        format!("expression has mode {found}, expected mode {expected}")
    }

    /// `check_place_rec`: a value that is not a place (a temporary), of a
    /// mode other than exec, used by exec code.
    #[must_use]
    pub fn temporary_in_exec(mode: &str) -> String {
        format!("cannot use {mode}-mode expression in executable context")
    }

    /// `check_place_rec`: a place (a variable or a field) of a mode other
    /// than exec, used by exec code.
    #[must_use]
    pub fn place_in_exec(mode: &str) -> String {
        format!("cannot access {mode}-mode place in executable context")
    }

    /// `ExprX::If`: an `if` in exec code whose condition is not exec.
    pub const CONDITION_NOT_EXEC: &str = "condition must have mode exec";

    /// `ExprX::Call`: a function called where its mode is not allowed.
    /// `function` is Verus's friendly path (`test_crate::f`).
    #[must_use]
    pub fn call_mode(function: &str, mode: &str) -> String {
        format!("cannot call function `{function}` with mode {mode}")
    }

    /// `ExprX::Assign`: an assignment from code whose mode is above the
    /// variable's (a proof block writing an exec variable).
    #[must_use]
    pub fn assign_mode(variable_mode: &str, code_mode: &str) -> String {
        format!("cannot assign to {variable_mode} variable from {code_mode} mode")
    }

    /// `ExprX::Assign`: an assignment in a spec function body, a clause or an
    /// assertion.
    pub const ASSIGN_IN_PURE: &str = "assignment is not allowed inside pure context";

    /// `get_var_loc_mode`: exec code assigning a ghost or tracked variable.
    pub const EXEC_MUTATES_NON_EXEC: &str = "exec code cannot mutate non-exec variable";

    /// `StmtX::Decl`: exec code initializing a ghost or tracked variable.
    pub const EXEC_INITIALIZES_NON_EXEC: &str = "exec code cannot initialize non-exec variables";

    /// `ExprX::Ghost`: a proof block inside ghost code.
    pub const ALREADY_PROOF: &str = "already in proof mode";
    /// `return` inside a `proof { .. }` block of spec code.
    pub const RETURN_IN_PROOF_IN_SPEC: &str = "return is not allowed inside spec";
    /// `return` inside the proof of an `assert .. by`.
    pub const RETURN_IN_ASSERT_BY: &str = "return is not allowed in 'assert ... by' statements";
    /// `ExprX::AssertBy` in exec code.
    pub const ASSERT_BY_IN_EXEC: &str = "cannot use 'assert ... by' in exec mode";
    /// Help attached to [`ASSERT_BY_IN_EXEC`].
    pub const ASSERT_BY_IN_EXEC_HELP: &str = "use a `proof` block";

    /// `ExprX::Return`: a `return` inside a proof block of an exec function.
    pub const RETURN_FROM_NON_EXEC: &str = "cannot return from non-exec code in exec function";
    /// `ExprX::Loop` in ghost code, at the loop's header.
    pub const LOOP_IN_GHOST: &str = "cannot use while in proof or spec mode";

    /// `ExprX::Return`: a `return` in a spec function body.
    pub const RETURN_IN_PURE: &str = "return is not allowed in pure context";

    /// `ExprX::AssertAssume`: `assert`, `assume` or `admit` outside ghost
    /// code.
    pub const ASSERT_IN_EXEC: &str = "cannot use assert or assume in exec mode";

    /// `ExprX::Quant` outside ghost code.
    pub const QUANT_IN_EXEC: &str = "cannot use forall/exists in exec mode";

    /// `ExprX::Choose` outside ghost code.
    pub const CHOOSE_IN_EXEC: &str = "cannot use choose in exec mode";

    /// `ExprX::Fuel`: a reveal outside ghost code, and its help line.
    pub const REVEAL_IN_EXEC: &str = "cannot use reveal/hide in exec mode";
    /// Help attached to [`REVEAL_IN_EXEC`].
    pub const REVEAL_IN_EXEC_HELP: &str = "wrap the reveal call in a `proof` block";

    /// `ExprX::VarAt`: `old(x)` in exec code.
    pub const OLD_IN_EXEC: &str = "cannot use `old` in exec-code";

    /// `check_one_expr`: pre-state values have no meaning in spec functions.
    pub const OLD_IN_SPEC: &str = "`old` is meaningless in spec functions";

    /// `ExprX::NeverToAny`: a diverging expression used as a spec value.
    pub const NEVER_TO_ANY_SPEC: &str = "never-to-any coercion is not allowed in spec mode";

    /// `get_variant_field` outside ghost code.
    pub const GET_VARIANT_IN_EXEC: &str = "cannot get variant in exec mode";
    pub const TEST_VARIANT_IN_EXEC: &str = "cannot test variant in exec mode";

    /// `check_function`: a parameter whose mode is below the function's.
    /// `name` is Verus's VIR variable (`x~2`).
    #[must_use]
    pub fn param_mode(name: &str, mode: &str) -> String {
        format!("parameter {name} cannot have mode {mode}")
    }

    /// `check_function`: a return value whose mode is below the function's.
    #[must_use]
    pub fn return_mode(mode: &str) -> String {
        format!("return type cannot have mode {mode}")
    }
}

/// `vir/src/ast_simplify.rs`, `ExprX::Assign` with an operator: a compound
/// assignment whose target is not a variable or a `&mut` parameter's
/// referent, such as a tuple or struct field.
pub const COMPOUND_ASSIGN_LHS: &str = "not yet implemented: lhs of compound assignment";

/// `vir/src/modes.rs`, `ExprX::Ghost`: a `proof { .. }` block whose type is
/// not `()`.
pub const PROOF_BLOCK_NOT_UNIT: &str = "proof block must have type ()";

/// `ast_to_sst.rs`, `expr_to_pure_exp_skip_checks`: a spec function body that
/// produces statements, which includes a body block without a tail
/// expression.
pub const EXPECTED_PURE: &str = "expected pure mathematical expression";

/// Errors `ast_to_sst.rs` reports for a loop (`ExprX::Loop`), each at the
/// loop's header, in the order it checks them.
pub mod loops {
    /// `#[verifier::allow_complex_invariants]` on a loop with isolation.
    pub const COMPLEX_WITH_ISOLATION: &str =
        "attribute 'allow_complex_invariants' can only be used with 'loop_isolation(false)'";
    /// `invariant_except_break` or `ensures` on a loop without isolation.
    pub const COMPLEX_WITHOUT_ALLOW: &str = "loop invariants with 'loop_isolation(false)' cannot \
        be invariant_except_break or ensures, unless #[verifier::allow_complex_invariants] is used";
    /// A loop without `decreases` outside an
    /// `exec_allows_no_decreases_clause` function.
    pub const NO_DECREASES: &str = "loop must have a decreases clause";
    /// Help attached to [`NO_DECREASES`].
    pub const NO_DECREASES_HELP: &str =
        "to disable this check, use #[verifier::exec_allows_no_decreases_clause] on the function";
}

/// `vir/src/well_formed.rs`, `check_function`: `assume_termination` under
/// `--no-cheating`.
pub const NO_CHEATING_ASSUME_TERMINATION: &str =
    "#[verifier::assume_termination] not allowed with --no-cheating";

/// `vir/src/recursion.rs`, `check_termination`: a function in a cycle of
/// calls without `decreases`, at its signature.
pub const RECURSION_WITHOUT_DECREASES: &str = "recursive function must have a decreases clause";

/// The help `check_termination` adds for an exec function.
pub const RECURSION_WITHOUT_DECREASES_EXEC_HELP: &str =
    "to disable this check, use #[verifier::exec_allows_no_decreases_clause] on the function";

/// Verus's rules on `decreases`, `when` and `decreases_by`
/// (`vir/src/well_formed.rs`, `check_function` and `check_crate`;
/// `vir/src/context.rs`, `GlobalCtx::new`; `vir/src/ast_to_sst.rs`).
pub mod termination {
    /// A `decreases_by` function that is not a proof function.
    pub const BY_NOT_PROOF: &str = "decreases_by/recommends_by function must have mode proof";
    /// A `decreases_by` function with a `decreases` clause.
    pub const BY_HAS_DECREASES: &str =
        "decreases_by/recommends_by function cannot have its own decreases clause";
    /// A `decreases_by` function with `requires`.
    pub const BY_HAS_REQUIRES: &str = "decreases_by/recommends_by function cannot have requires clauses (use decreases_when in the spec function instead)";
    /// A `decreases_by` function with `ensures`.
    pub const BY_HAS_ENSURES: &str =
        "decreases_by/recommends_by function cannot have ensures clauses";
    /// A `decreases_by` function with a return value.
    pub const BY_HAS_RETURN: &str =
        "decreases_by/recommends_by function cannot have a return value";
    /// A `decreases_by` function that is a trait method.
    pub const BY_TRAIT_METHOD: &str =
        "decreases_by/recommends_by function cannot be a trait method";
    /// `decreases_by` on a proof or exec function.
    pub const BY_NOT_SPEC: &str = "only spec functions can use decreases_by/recommends_by";
    /// `decreases_when` on a proof or exec function.
    pub const WHEN_NOT_SPEC: &str =
        "only spec functions can use decreases_when (use requires for proof/exec functions)";
    /// `decreases_when` without `decreases`.
    pub const WHEN_WITHOUT_DECREASES: &str = "decreases_when can only be used when there is a decreases clause (use recommends(...) for nonrecursive functions)";
    /// A `decreases_by` naming a function without the attribute.
    pub const BY_NOT_MARKED: &str = "proof function must be marked #[verifier::decreases_by] or #[verifier::recommends_by] to be used as decreases_by/recommends_by";
    /// One function named by two `decreases_by`.
    pub const BY_USED_TWICE: &str =
        "same proof function used for two different decreases_by/recommends_by";
    /// A `decreases_by` function in another module.
    pub const BY_OTHER_MODULE: &str =
        "a decreases_by function must be in the same module as the function definition";
    /// A `decreases_by` function no `decreases_by` names.
    pub const BY_UNUSED: &str = "function cannot be marked #[verifier::decreases_by] or #[verifier::recommends_by] unless it is used in some decreases_by/recommends_by";
    /// A trait method's default body with a measure.
    pub const DEFAULT_METHOD_DECREASES: &str =
        "trait default methods do not yet support recursion and decreases";
    /// A call of a `decreases_by` function.
    pub const BY_CALLED: &str = "cannot call a decreases_by/recommends_by function directly";
    /// A `decreases_by` function on a cycle of the call graph.
    pub const BY_CYCLE: &str = "found cyclic dependency in decreases_by function";
    /// A `proof { .. }` block of spec code outside the body of a spec
    /// function with a measure.
    pub const PROOF_IN_SPEC_UNSUPPORTED: &str = "proof blocks inside spec code is currently supported only for spec functions with decreases";
    /// A `proof { .. }` block in a spec function with a measure that is not
    /// recursive.
    pub const PROOF_IN_SPEC_NOT_RECURSIVE: &str =
        "proof blocks inside spec code is currently supported only for recursion";
    /// An explicit `return` in a `decreases_by` function.
    pub const BY_RETURN: &str = "explicit returns are not allowed in decreases_by function";
    /// `reveal_with_fuel` above 1 of a function that is not recursive.
    pub const FUEL_NOT_RECURSIVE: &str =
        "this function is not recursive (nor mutually recursive), so fuel cannot be set to more than 1";
    /// The warning on an exec function with a measure that allows none.
    pub const EXEC_DECREASES_WARNING: &str = "if exec_allows_no_decreases_clause is set, decreases checks in exec functions do not guarantee termination of functions with loops";

    /// `check_var`: a measure that reads the `&mut` parameter `name`
    /// without `old`.
    #[must_use]
    pub fn decreases_mut_ref(name: &str) -> String {
        format!(
            "in decreases clause, use `old({name})` to refer to the pre-state of an &mut variable"
        )
    }

    /// `read_header`: a second header of one kind (`slot` is `decreases`,
    /// `decreases_when` or `decreases_by`).
    #[must_use]
    pub fn second_header(slot: &str) -> &'static str {
        match slot {
            "decreases" => "only one decreases expression currently supported",
            "decreases_when" => "only one if decrease_when expression currently supported",
            _ => "only one decreases_by expression currently supported",
        }
    }

    /// `check_functions_match`, between a `decreases_by` function and its
    /// spec function: `what` is `type parameters`, `type bounds`, `number
    /// of parameters` or `parameters`.
    #[must_use]
    pub fn by_mismatch(what: &str) -> String {
        format!("decreases_by/recommends_by function should have the same {what}")
    }
}

/// `vir/src/recursive_types.rs`, `scc_error`: a cycle through a trait or a
/// trait implementation.
pub const TRAIT_CYCLE: &str =
    "found a cyclic self-reference in a definition, which may result in nontermination";

/// `vir/src/recursive_types.rs`, `check_recursive_types`: a datatype none
/// of whose variants can be built without the datatype itself, at the
/// datatype.
pub const NO_BASE_VARIANT: &str = "datatype must have at least one non-recursive variant";

/// Verus's errors for trait method declarations and implementations.
pub mod traits {
    /// `vir/src/headers.rs`, `make_trait_decls`: a `VERUS_SPEC__f` without
    /// a method `f`, at the specification method's signature.
    pub const NO_MATCHING_METHOD: &str = "no matching method found for method specification";
    /// `make_trait_decl`: the specification method and the method differ.
    pub const SPEC_PARAM_COUNT: &str =
        "method specification has different number of parameters from method";
    /// `make_trait_decl`.
    pub const SPEC_PARAMS: &str = "method specification has different parameters from method";
    /// `make_trait_decl`.
    pub const SPEC_TYPE_PARAM_COUNT: &str =
        "method specification has different number of type parameters from method";
    /// `make_trait_decl`.
    pub const SPEC_TYPE_PARAMS: &str =
        "method specification has different type parameters from method";
    /// `make_trait_decl`.
    pub const SPEC_RETURN: &str = "method specification has a different return from method";
    /// `rust_to_vir_func.rs`, `check_item_fn`: a specification method whose
    /// body does not end in `no_method_body()`.
    pub const SPEC_WITHOUT_NO_METHOD_BODY: &str =
        "trait method declaration body must end with call to no_method_body()";
    /// `check_item_fn`: `no_method_body()` outside a specification method.
    pub const NO_METHOD_BODY_OUTSIDE_DECL: &str =
        "no_method_body can only appear in trait method declarations";
    /// `vir/src/headers.rs`, `read_header_block`: `no_method_body();` as a
    /// statement.
    pub const NO_METHOD_BODY_STATEMENT: &str =
        "no_method_body() must be a method's final expression, with no semicolon";
    /// `read_header`: statements between the header and `no_method_body()`.
    pub const NO_METHOD_BODY_AFTER_STATEMENTS: &str =
        "no statements are allowed before no_method_body()";
    /// `check_item_fn`: `open` or `closed` on a declaration without a body.
    pub const OPEN_ON_DECL: &str =
        "trait function declarations cannot be open or closed, as they don't have a body";
    /// `check_item_fn`: a spec method with a body, of a trait visible
    /// outside its module, without `open` or `closed`.
    pub const OPEN_CLOSED_REQUIRED: &str =
        "open/closed is required for implementations of non-private traits";
    /// `vir/src/well_formed.rs`, `check_function`: `requires` on a method
    /// implementing a trait method, at its signature.
    pub const IMPL_REQUIRES: &str = "trait method implementation cannot declare requires clauses; these can only be inherited from the trait declaration";
    /// `check_function`.
    pub const IMPL_OPENS_INVARIANTS: &str = "trait method implementation cannot declare an opens_invariants spec; this can only be inherited from the trait declaration";
    /// `check_function`.
    pub const IMPL_UNWIND: &str = "trait method implementation cannot declare an unwind specification; this can only be inherited from the trait declaration";
    /// `check_function`: the declaration is `uninterp`.
    pub const IMPL_UNINTERP: &str = "trait method implementation cannot be marked as `uninterp`";
    /// `check_function`.
    pub const DECL_NO_DECREASES_ALLOWED: &str =
        "trait method declaration cannot declare exec_allows_no_decreases_clause";
    /// `vir/src/traits.rs`, `demote_external_traits`.
    pub const DROP_REQUIRES: &str = "requires are not allowed on the implementation for Drop";
    /// `demote_external_traits`.
    pub const DROP_OPENS_INVARIANTS: &str =
        "the implementation for Drop must be marked opens_invariants none";
    /// `demote_external_traits`.
    pub const DROP_NO_UNWIND: &str = "the implementation for Drop must be marked no_unwind";
    /// `vir/src/traits.rs`, `check_modes`.
    pub const EXTERNAL_TRAIT_MODE: &str = "function for external trait must have mode 'exec'";
    /// `vir/src/well_formed.rs`, `check_function`: Verus's copy of a
    /// default method for an implementation outside the method's module,
    /// whose body is visible more widely than the copy (`internal_err!`), at
    /// the default method.
    pub const INHERITED_BODY_MORE_PUBLIC: &str =
        "verus internal error: the function body is more public than the function itself";
    /// `rust_verify/src/external.rs`, which checks it before
    /// `rust_to_vir_trait.rs` would.
    pub const EXTERNAL_TRAIT_ITEM: &str = "a trait item cannot be marked 'external'. Perhaps you meant to mark the entire trait external?";
    /// `rust_verify/src/external.rs`. Keep both established summaries of
    /// this rule in the same diagnostic for every trait implementation.
    pub const EXTERNAL_IMPL_ITEM: &str = "an item in a trait impl cannot be marked 'external'. An individual item of a trait impl cannot be marked external independently of the implementation. Perhaps you meant to mark the entire trait impl external, or you meant to mark this item as `external_body`?";
    /// `vir/src/modes.rs`, `check_function`: a trait method implemented in
    /// another mode.
    #[must_use]
    pub fn impl_mode(expected: &str) -> String {
        format!("function must have mode {expected}")
    }
    /// `check_function`: a parameter of an implementation in another mode
    /// than the declaration's, at the parameter.
    #[must_use]
    pub fn impl_param_mode(expected: &str) -> String {
        format!("parameter must have mode {expected}")
    }
    /// `check_function`: the return value of an implementation in another
    /// mode than the declaration's.
    #[must_use]
    pub fn impl_return_mode(expected: &str) -> String {
        format!("function return value must have mode {expected}")
    }
}

/// Errors of Verus's attribute parser (`rust_verify/src/attributes.rs`) and
/// of the attribute checks on an expression (`rust_to_vir_expr.rs`,
/// `expr_to_vir` and `expr_to_vir_innermost`). Each is reported at the
/// attribute, except [`attr::TRUNCATE_NOT_CAST`], which is reported at the
/// expression.
pub mod attr {
    /// `attr_to_tree`: `verifier` alone, or arguments that are not names
    /// and literals.
    pub const INVALID_VERIFIER: &str = "invalid verifier attribute";
    /// `attr_to_tree`: `verus::internal` without exactly one name or
    /// literal in parentheses.
    pub const INVALID_VERUS: &str = "invalid verus attribute";
    /// `attr_to_tree`: the old bare mode attributes.
    pub const OLD_MODE_ATTRIBUTE: &str =
        "attributes spec, proof, exec are not supported anymore; use the verus! macro instead";
    /// `parse_attrs`: a `verifier::` keyword or argument shape Verus does not
    /// know.
    pub const UNRECOGNIZED_VERIFIER: &str = "unrecognized verifier attribute";
    /// `parse_attrs`: a `verus::internal(..)` keyword Verus does not know,
    /// or `verus::<name>` other than `verus::trusted`.
    pub const UNRECOGNIZED_INTERNAL: &str = "unrecognized internal attribute";
    /// `get_proof_note_label`: a proof note or custom error whose argument
    /// is not one plain string literal.
    pub const EXPECTED_STRING: &str = "expected exactly one argument, a string literal";
    /// `parse_attrs`: `trigger()`.
    pub const EMPTY_TRIGGER: &str = "expected either #[trigger] or non-empty #[trigger(...)]";
    /// `parse_attrs`: `auto_ext_equal(..)` with a place Verus does not know.
    pub const AUTO_EXT_EQUAL_PLACES: &str =
        "expected `assert`, `assert_by`, and/or `ensures` for auto_ext_equal";
    /// `get_rlimit_arg`.
    pub const RLIMIT_NUMBER: &str = "expected number, or `infinity` for rlimit";
    /// `parse_attrs`: the attribute the macro writes for a misplaced
    /// `#[trigger ..]`.
    pub const INVALID_TRIGGER_ATTRIBUTE: &str = "invalid trigger attribute: to provide a trigger expression, use the #![trigger <expr>] attribute";
    /// `parse_attrs`: `verus::internal(prover(..))` naming no prover.
    pub const INVALID_PROVER: &str = "invalid prover";
    /// `expr_to_vir_innermost`: `verifier::truncate` on an expression that
    /// is not a cast.
    pub const TRUNCATE_NOT_CAST: &str = "the attribute #[verifier::truncate] is only allowed on casts (you may need parentheses around the cast)";
    /// `get_proof_note_annotation`: a second proof note or custom error on
    /// one expression, reported at the second.
    pub const DUPLICATE_NOTE: &str = trust_vc_vcir::wf::MSG_DUPLICATE_NOTE;
    /// `expr_to_loc_coerce_modes`: the location of a place that is a
    /// temporary, such as an assignment target wrapped in a trigger or
    /// proof note.
    pub const COMPLEX_MUT_ARG: &str =
        "complex arguments to &mut parameters are currently unsupported";

    /// `get_trigger_arg`: a trigger group that is not an integer; `found`
    /// is Verus's `{:?}` of the argument.
    #[must_use]
    pub fn trigger_not_integer(found: &str) -> String {
        format!("expected integer constant, found {found}")
    }
}

/// The span label Verus adds for a `#[verifier::proof_note("text")]`
/// (`vir/src/messages.rs`, `proof_note_label`).
#[must_use]
pub fn proof_note_label(text: &str) -> String {
    format!("note: {text}")
}

/// Messages and labels of verification failures, for the reporter that turns
/// per-site verdicts into diagnostics. Each is what the reference Verus run
/// printed for the named basic.rs case.
pub mod failure {
    /// Message and primary label of a failed `assert` (`test1_fails`).
    pub const ASSERTION_FAILED: &str = "assertion failed";
    /// Message of a call whose precondition fails (`test_requires2`).
    pub const PRECONDITION_NOT_SATISFIED: &str = "precondition not satisfied";
    /// Label on the failing `requires` clause (`test_requires2`).
    pub const FAILED_PRECONDITION: &str = "failed precondition";
    /// Message of a failed postcondition (`test_ret`).
    pub const POSTCONDITION_NOT_SATISFIED: &str = "postcondition not satisfied";
    /// Primary label on the failing `ensures` clause (`test_ret`).
    pub const FAILED_THIS_POSTCONDITION: &str = "failed this postcondition";
    /// Secondary label on the returned expression (`test_ret`).
    pub const AT_END_OF_BODY: &str = "at the end of the function body";
    /// Label on an explicit `return` whose postcondition fails.
    pub const AT_THIS_EXIT: &str = "at this exit";
    /// Exec `+ - *` that can leave its type (`test_compound_assign_fail`).
    pub const ARITH_OVERFLOW: &str = "possible arithmetic underflow/overflow";
    /// Exec `/ %` whose divisor can be zero (`test_compound_assign_fail`).
    pub const DIVISION_BY_ZERO: &str = "possible division by zero";
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn phases_order_like_verus() {
        assert!(Phase::RustToVir < Phase::WellFormed);
        assert!(Phase::WellFormed < Phase::Modes);
        assert!(Phase::Modes < Phase::Simplify);
        assert!(Phase::Simplify < Phase::Sst);
        assert!(Phase::Sst < Phase::SstElaboration);
        assert!(Phase::Sst.is_sst() && Phase::SstElaboration.is_sst());
        assert!(!Phase::Simplify.is_sst());
    }

    #[test]
    fn texts() {
        assert_eq!(
            unsupported("mut self"),
            "The verifier does not yet support the following Rust feature: mut self"
        );
        assert_eq!(spec_eq_type_label("u64"), "this is `u64`");
        assert_eq!(proof_note_label("Property 732"), "note: Property 732");
        assert_eq!(pattern_mode("proof"), "pattern cannot have mode proof");
        // The texts the reference run printed.
        assert_eq!(
            wf::private_reference(wf::REASON_OPEN_SPEC, "function"),
            "in pub open spec function, cannot refer to private function"
        );
        assert_eq!(
            wf::private_reference(wf::REASON_REQUIRES, "function"),
            "in 'requires' clause of public function, cannot refer to private function"
        );
        assert_eq!(
            wf::opaque_datatype("field expression").0,
            "disallowed: field expression for an opaque datatype"
        );
        assert_eq!(
            wf::access_help(
                wf::REASON_REQUIRES,
                "field expression",
                "everywhere",
                "test_crate"
            ),
            "note that because this is a 'requires' clause of public function, this field \
             expression must be well-formed everywhere, which is wider than `test_crate`"
        );
        assert!(wf::reveal_closed("test_crate::m::foo").starts_with(
            "reveal/fuel statement is not allowed here because the function `test_crate::m::foo` \
             is marked 'closed' and thus its body is not visible here"
        ));
    }
}
