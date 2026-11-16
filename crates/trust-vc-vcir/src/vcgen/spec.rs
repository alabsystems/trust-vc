//! Crate-wide solver vocabulary: spec functions, clip functions and the
//! uninterpreted stand-ins for nonlinear arithmetic.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Every query of a crate declares the same functions:
//!
//! * One per scalar leaf of a spec function's result, over its flattened
//!   parameters. A scalar result uses `sf<i>`; product leaves use
//!   `sf<i>_<leaf>`. Each definition, when it has one, is the
//!   translated body. Where the function is revealed (non-opaque functions
//!   from the start, opaque ones after `reveal`), the generator inlines its
//!   calls; elsewhere a call is an uninterpreted application. A spec
//!   function returning a product with no scalar leaves needs no solver function.
//! * `clip_<ty>_oob` for every supported machine type and `nat`. Verus reads
//!   `x as T` as `clip_T(x)`: a value in range is unchanged, any other value
//!   maps to some value in range, fixed for that input. The generator writes
//!   it as `if x in range { x } else { clip_T_oob(x) }` and states the range
//!   of every `clip_T_oob` application that occurs in a query, which is
//!   exactly what Verus's clip axioms give.
//! * `nl_mul`, `nl_div`, `nl_mod`: nonlinear products and quotients, see
//!   `super::expr`.
//!
//! Calls of functions with a bounded result (a spec function returning a
//! machine integer or `nat`, and the clip choosers) get a range fact at every
//! occurrence, as Verus's return-type axioms give for arguments in range.
//!
//! Definitions are inlined by the generator rather than handed to the
//! solver as equations: the terms stay first order and quantifier free, and
//! the range and axiom instances above can be read off the final terms.
//!
//! A spec function with a `decreases` measure has a definition that holds
//! only where Verus's `def_reqs` hold (`sst_to_air_func.rs`,
//! `func_body_to_air`): the parameters' type facts and the `when`
//! condition. Inlining such a call gives `if guard { body } else { call }`.
//!
//! Recursive spec functions (members of a [`crate::RecGroup`]) follow
//! Verus's fuel encoding (`func_body_to_air`, the `rec%f` axioms). Each has
//! a second solver function, `rf<i>`, standing for `rec%f` at every fuel
//! (`rec%f(x, fuel) == rec%f(x, zero)`). Its definition is the body with the
//! calls of its group's members turned into their `rf` functions. A call
//! `sf<i>(x)` of a revealed member is `rf<i>(x)` where the guard holds, and
//! `rf<i>(x)` unfolds into the body as many times as Verus's fuel lets Z3
//! unfold it: the member's cycle length plus `n - 1` after
//! `reveal_with_fuel(f, n)` along each chain of unfoldings ([`unfold`]). The
//! unfoldings are facts about the applications, not substitutions, so an
//! application that is not unfolded in one place still equals its unfolding
//! elsewhere, as fuel-irrelevance gives in Verus. An application unfolds
//! only where Z3 would instantiate on it: where it survives Z3's rewriting
//! and is relevant (`super::relevance`).
//!
//! A spec function's definition is only admitted if it is not circular
//! outside a declared group: a function that reaches itself through other
//! spec functions, other than through the members of its own group, is
//! refused. A function whose definition depends on a refused one is
//! refused too, since leaving the dependency uninterpreted would be weaker
//! than Verus and turn provable code into failures.

use std::collections::{BTreeSet, HashMap};

use crate::ids::FnId;
use crate::item::{Body, FnDecl, FnRole, Mode, VcCrate};
use crate::ty::IntRange;
use crate::CheckedSpecDefinitions;

use super::expr::{Reads, Tr, R};
use super::query::{Function, VcRefusal};
use super::relevance::Analysis;
use super::term::{Sort, Term};
use super::type_encoding::{TypeArgument, TypeEnv};
use super::val::{range_bounds, refusal, Ctx, LeafTy, Shape, Val};

/// Uninterpreted product of two non-constant integers.
pub(crate) const NL_MUL: &str = "nl_mul";
/// Uninterpreted Euclidean quotient by a non-constant divisor.
pub(crate) const NL_DIV: &str = "nl_div";
/// Uninterpreted Euclidean remainder by a non-constant divisor.
pub(crate) const NL_MOD: &str = "nl_mod";

/// Integer types that have a clip function.
pub(super) const CLIP_RANGES: [IntRange; 11] = [
    IntRange::U(8),
    IntRange::U(16),
    IntRange::U(32),
    IntRange::U(64),
    IntRange::U(128),
    IntRange::I(8),
    IntRange::I(16),
    IntRange::I(32),
    IntRange::I(64),
    IntRange::I(128),
    IntRange::Nat,
];

/// Solver name of the out-of-range chooser of the clip into `range`.
pub(crate) fn clip_oob_name(range: IntRange) -> String {
    match range {
        IntRange::U(bits) => format!("clip_u{bits}_oob"),
        IntRange::I(bits) => format!("clip_i{bits}_oob"),
        IntRange::Nat => "clip_nat_oob".to_string(),
        // Never used for other types (`clip` refuses them first); the name
        // keeps the function total.
        _ => "clip_unsupported_oob".to_string(),
    }
}

/// `v as range`, in Verus's reading: `v` if it fits, the chosen in-range
/// value for `v` otherwise.
pub(crate) fn clip(range: IntRange, v: Term) -> Term {
    let (lo, hi) = range_bounds(range);
    let chosen = Term::call(clip_oob_name(range), vec![v.clone()], Sort::Int);
    Term::ite(v.within_type_bounds(lo, hi), v, chosen)
}

/// A descriptor minted by the actual mathematical clipping producer. It
/// transports trigger metadata, never a new function/axiom or source license.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct ClipPattern {
    range: IntRange,
    term: Term,
}

impl ClipPattern {
    pub(super) fn into_parts(self) -> (IntRange, Term) {
        (self.range, self.term)
    }
}

pub(super) fn clip_pattern(range: IntRange, value: Term) -> Option<ClipPattern> {
    if value.sort() != super::term::Sort::Int || !CLIP_RANGES.contains(&range) {
        return None;
    }
    Some(ClipPattern {
        range,
        term: clip(range, value),
    })
}

/// Verify the WHOLE existing ABI, including exact range predicate, branches,
/// operand and generated fallback. This is not a name-only recognizer. The
/// caller's existing meter prepays copies/comparisons before construction.
pub(super) fn clip_fallback<'a>(
    term: &'a Term,
    range: IntRange,
    pay: &mut impl FnMut(usize) -> bool,
) -> Option<&'a Term> {
    if !pay(4) || !CLIP_RANGES.contains(&range) {
        return None;
    }
    let Term::Ite(_, value, fallback, super::term::Sort::Int) = term else {
        return None;
    };
    if value.sort() != super::term::Sort::Int {
        return None;
    }
    if !super::closed_templates::charge_term(term, pay)
        || !super::closed_templates::charge_term(term, pay)
        || !super::closed_templates::charge_term(term, pay)
    {
        return None;
    }
    let expected = clip(range, (**value).clone());
    if expected != *term {
        return None;
    }
    match &**fallback {
        Term::Call {
            args,
            sort: super::term::Sort::Int,
            ..
        } if args.len() == 1 && args[0].sort() == super::term::Sort::Int => Some(fallback),
        _ => None,
    }
}

/// The signature of a spec function as the solver sees it.
#[derive(Debug, Clone)]
pub(crate) struct SpecSig {
    pub(crate) owner: FnId,
    /// Generic declarations use the pinned boxed argument ABI. Closed
    /// monomorphic declarations retain its existing native specialization.
    pub(crate) boxed_params: bool,
    /// Number of type parameters; each contributes a Decoration and TypeId
    /// argument before the value arguments.
    pub(crate) n_types: usize,
    /// Layout of each parameter.
    pub(crate) params: Vec<Shape>,
    /// The complete product layout of the result, including empty products.
    pub(crate) result: Shape,
    /// Solver functions for the result's scalar leaves, in layout order.
    pub(crate) outputs: Vec<SpecOutput>,
    /// Why calls of this function cannot be translated, if they cannot.
    pub(crate) problem: Option<VcRefusal>,
}

/// One scalar result of a spec function, with its declared type information.
#[derive(Debug, Clone)]
pub(crate) struct SpecOutput {
    pub(crate) name: String,
    pub(crate) leaf: LeafTy,
}

/// A spec function's definition, over the parameters `a0`, `a1`, ...
#[derive(Debug, Clone)]
pub(crate) struct SpecDef {
    /// The solver function defined.
    pub(crate) function: String,
    /// Parameter names and sorts; the only free variables of `guard` and
    /// `body`.
    pub(crate) params: Vec<(String, Sort)>,
    /// Where the definition holds: Verus's `def_reqs` for a function with a
    /// measure, `true` otherwise.
    pub(crate) guard: Term,
    /// The defining term.
    pub(crate) body: Term,
}

/// A recursive spec function's fixpoint.
#[derive(Debug, Clone)]
pub(crate) struct RecDef {
    /// The definition of `rf<i>`; its recursive calls are applications of
    /// the group's `rf` functions.
    pub(crate) def: SpecDef,
    /// The function's own solver name (`sf<i>`), which a call from outside
    /// the group applies.
    pub(crate) spec_name: String,
    /// The parameter typing invariants, independent of `decreases_when`.
    /// Verus's recursive return-type axiom holds under this guard at every
    /// fuel, including zero; the stronger body guard does not apply to it.
    pub(crate) type_guard: Term,
    /// Bounds of a scalar result, if its type has bounds.
    pub(crate) return_bounds: Option<(Option<i128>, Option<u128>)>,
    /// Boxed result predicate over the definition parameters and `result_value`.
    pub(crate) return_predicate: Option<Term>,
    /// The length of the shortest cycle back to the function: how many
    /// times a call unfolds with fuel 1.
    pub(crate) cycle: u32,
    /// The result sort.
    pub(crate) sort: Sort,
}

/// A declaration's result typing, guarded by its actual parameter predicates.
#[derive(Debug, Clone)]
pub(crate) struct TypingSchema {
    pub(crate) params: Vec<(String, Sort)>,
    pub(crate) guard: Term,
    pub(crate) predicate: Term,
}

impl TypingSchema {
    pub(crate) fn instantiate(&self, args: &[Term]) -> Option<Term> {
        if args.len() != self.params.len()
            || self
                .params
                .iter()
                .zip(args)
                .any(|((_, sort), arg)| *sort != arg.sort())
        {
            return None;
        }
        let substitutions = self
            .params
            .iter()
            .map(|(name, _)| name.as_str())
            .zip(args.iter().cloned())
            .collect();
        Some(Term::implies(
            self.guard.substitute(&substitutions),
            self.predicate.substitute(&substitutions),
        ))
    }
}

/// Everything the queries of one crate share.
pub(crate) struct Tables {
    pub(crate) sigs: HashMap<FnId, SpecSig>,
    /// The definition of each non-recursive spec function that has one.
    pub(crate) defs: HashMap<FnId, Vec<SpecDef>>,
    /// The fixpoint of each recursive spec function that has a usable one.
    pub(crate) rec_defs: HashMap<FnId, Vec<RecDef>>,
    /// The function each fixpoint function (`rf<i>`) belongs to.
    rec_names: HashMap<String, (FnId, usize)>,
    /// Functions declared in every query.
    pub(crate) functions: Vec<Function>,
    pub(crate) typings: HashMap<String, TypingSchema>,
    /// Scalar result names belonging to one logical application. Spec and
    /// recursive helpers have separate identities until their guarded bridge.
    pub(crate) families: HashMap<String, (FnId, bool)>,
    /// Functions whose every application has a range: solver name to
    /// bounds.
    pub(crate) ranged: HashMap<String, (Option<i128>, Option<u128>)>,
}

/// A scalar function, or one leaf of a product function's result.
fn result_name(prefix: &str, index: usize, result: &Shape, leaf: usize) -> String {
    if matches!(result, Shape::Leaf(_)) {
        format!("{prefix}{index}")
    } else {
        format!("{prefix}{index}_{leaf}")
    }
}

impl Tables {
    #[cfg(test)]
    pub(crate) fn build(ctx: &Ctx<'_>, krate: &VcCrate) -> Self {
        Self::build_with_spec_definitions(ctx, krate, &CheckedSpecDefinitions::default())
    }

    pub(crate) fn build_with_spec_definitions(
        ctx: &Ctx<'_>,
        krate: &VcCrate,
        definitions: &CheckedSpecDefinitions,
    ) -> Self {
        let mut functions = Vec::new();
        let mut families = HashMap::new();
        let mut ranged = HashMap::new();
        for name in [NL_MUL, NL_DIV, NL_MOD] {
            functions.push(Function {
                name: name.to_string(),
                params: vec![Sort::Int, Sort::Int],
                ret: Sort::Int,
            });
        }
        for range in CLIP_RANGES {
            let name = clip_oob_name(range);
            functions.push(Function {
                name: name.clone(),
                params: vec![Sort::Int],
                ret: Sort::Int,
            });
            ranged.insert(name, range_bounds(range));
        }

        let spec_fns: Vec<&FnDecl> = krate.fns.iter().filter(|d| d.mode == Mode::Spec).collect();
        let mut sigs = HashMap::new();
        let mut rec_names: HashMap<FnId, Vec<String>> = HashMap::new();
        for (index, decl) in spec_fns.iter().enumerate() {
            let sig = signature(ctx, decl, index);
            if sig.problem.is_none() {
                let mut params: Vec<Sort> = (0..sig.n_types)
                    .flat_map(|_| [Sort::Decoration, Sort::TypeId])
                    .collect();
                for shape in &sig.params {
                    let mut leaves = Vec::new();
                    shape.leaves(&mut leaves);
                    params.extend(leaves.iter().map(|leaf| leaf.sort()));
                }
                let mut recursive = Vec::new();
                for (leaf, output) in sig.outputs.iter().enumerate() {
                    let ret = output.leaf.sort();
                    functions.push(Function {
                        name: output.name.clone(),
                        params: params.clone(),
                        ret,
                    });
                    families.insert(output.name.clone(), (decl.id, false));
                    if ctx.group(decl.id).is_some() {
                        let name = result_name("rf", index, &sig.result, leaf);
                        functions.push(Function {
                            name: name.clone(),
                            params: params.clone(),
                            ret,
                        });
                        families.insert(name.clone(), (decl.id, true));
                        recursive.push(name);
                    }
                    if let LeafTy::Int(range) = output.leaf {
                        if range != IntRange::Int
                            && sig.n_types == 0
                            && decl.role != FnRole::Imported
                        {
                            ranged.insert(output.name.clone(), range_bounds(range));
                        }
                    }
                }
                if !recursive.is_empty() {
                    rec_names.insert(decl.id, recursive);
                }
            }
            sigs.insert(decl.id, sig);
        }

        let mut typings = HashMap::new();
        for decl in &spec_fns {
            let Some(sig) = sigs
                .get(&decl.id)
                .filter(|sig| sig.problem.is_none())
                .cloned()
            else {
                continue;
            };
            let (types, values, params) = definition_params(&sig);
            let guard = parameter_types(ctx, &sig, &types, &values);
            for output in &sig.outputs {
                let app = Term::call(
                    output.name.clone(),
                    params
                        .iter()
                        .map(|(name, sort)| Term::var(name.clone(), *sort))
                        .collect(),
                    output.leaf.sort(),
                );
                match guard.clone().and_then(|guard| {
                    ctx.type_fact(output.leaf, &types, &app, decl.span)
                        .map(|predicate| TypingSchema {
                            params: params.clone(),
                            guard,
                            predicate,
                        })
                }) {
                    Ok(schema) => {
                        typings.insert(output.name.clone(), schema);
                    }
                    Err(problem) => {
                        if let Some(sig) = sigs.get_mut(&decl.id) {
                            sig.problem = Some(problem);
                        }
                        break;
                    }
                }
            }
        }

        // Bodies. Calls inside a body only need signatures, so every body
        // can be translated before any status is final.
        let mut defs: HashMap<FnId, Vec<SpecDef>> = HashMap::new();
        let mut rec_defs: HashMap<FnId, Vec<RecDef>> = HashMap::new();
        let mut callees: HashMap<FnId, BTreeSet<FnId>> = HashMap::new();
        let mut problems: HashMap<FnId, VcRefusal> = HashMap::new();
        'bodies: for signature in &spec_fns {
            // The current client owns the signature and solver identity. A
            // separately checked definition keeps its own coherent local
            // scope; no body or clause is installed on the imported FnDecl.
            let decl = definitions.get(signature.id).unwrap_or(*signature);
            let Some(sig) = sigs.get(&decl.id) else {
                continue;
            };
            if sig.problem.is_some() {
                continue;
            }
            // Explicit inline bodies are elaborated from their checked source
            // expression at each call. Publishing a second generic UF body
            // would translate its unspecialized binders and choices instead.
            // Signatures, typing schemas, WF and cycle checks still apply;
            // imported and trait-dispatch bodies never acquire this grant.
            if decl.attrs.inline && decl.role != FnRole::TraitDecl && decl.role != FnRole::Imported
            {
                continue;
            }
            match &decl.body {
                Body::Spec(expr) | Body::Constant(expr) => {
                    let (types, param_vals, params) = definition_params(sig);
                    let type_guard = match parameter_types(ctx, sig, &types, &param_vals) {
                        Ok(guard) => guard,
                        Err(problem) => {
                            problems.insert(decl.id, problem);
                            continue;
                        }
                    };
                    let mut native_params = Vec::new();
                    for (id, value) in decl.params.iter().zip(&param_vals) {
                        let Some(local) = decl.local(*id) else {
                            continue 'bodies;
                        };
                        let native = if sig.boxed_params {
                            ctx.native_value(&local.ty, &types, value.clone(), local.span)
                        } else {
                            Ok(value.clone())
                        };
                        match native {
                            Ok(value) => native_params.push(value),
                            Err(problem) => {
                                problems.insert(decl.id, problem);
                                continue 'bodies;
                            }
                        }
                    }
                    let reads = Reads {
                        local_types: Reads::decl_types(decl),
                        read: decl.params.iter().copied().zip(native_params).collect(),
                        old: HashMap::new(),
                        types,
                        ..Reads::default()
                    };
                    let mut tr = Tr::new(ctx, &sigs, &functions, &reads);
                    let value = match tr.expr(expr) {
                        Ok(value) => value,
                        Err(problem) => {
                            problems.insert(decl.id, problem);
                            continue;
                        }
                    };
                    // Verus's `def_reqs`, for a function with a measure.
                    let guard = if decl.decreases.is_empty() {
                        Ok(Term::Bool(true))
                    } else {
                        def_reqs(&mut tr, &type_guard, decl)
                    };
                    callees.insert(decl.id, tr.called.clone());
                    let guard = match guard {
                        Ok(guard) => guard,
                        Err(problem) => {
                            problems.insert(decl.id, problem);
                            continue;
                        }
                    };
                    // A native initializer supplies a value only where every
                    // checked operation is defined and the entire result fits
                    // its declared type. These are guards, never assumptions
                    // used to prove the initializer's own obligations.
                    let guard = if matches!(decl.body, Body::Constant(_)) {
                        let mut validity = vec![guard];
                        validity.extend(tr.checks.iter().map(|check| {
                            Term::implies(Term::and(check.guard.clone()), check.cond.clone())
                        }));
                        let mut leaves = Vec::new();
                        value.leaves(&mut leaves);
                        for (output, term) in sig.outputs.iter().zip(&leaves) {
                            match ctx.type_fact(output.leaf, &reads.types, term, expr.span) {
                                Ok(predicate) => validity.push(predicate),
                                Err(problem) => {
                                    problems.insert(decl.id, problem);
                                    continue 'bodies;
                                }
                            }
                        }
                        Term::and(validity)
                    } else {
                        guard
                    };
                    // A trait's default body is what an implementation that
                    // does not override the method gets (through an
                    // instance); a call through the declaration may reach
                    // an overriding implementation, so the declaration has
                    // no definition.
                    if decl.role == FnRole::TraitDecl {
                        continue;
                    }
                    if !value.matches(&sig.result) {
                        problems.insert(
                            decl.id,
                            refusal(
                                "vcgen-internal",
                                "a spec body of the wrong shape",
                                expr.span,
                            ),
                        );
                        continue;
                    }
                    let mut bodies = Vec::new();
                    value.leaves(&mut bodies);
                    match (rec_names.get(&decl.id), ctx.cycle_len(decl.id)) {
                        (Some(recursive), Some(cycle)) => {
                            // The calls of the group's members are calls of
                            // their fixpoints.
                            let mut group_names = HashMap::new();
                            for (id, names) in &rec_names {
                                if ctx.same_group(decl.id, *id) {
                                    if let Some(signature) = sigs.get(id) {
                                        for (output, name) in signature.outputs.iter().zip(names) {
                                            group_names.insert(output.name.as_str(), name.as_str());
                                        }
                                    }
                                }
                            }
                            let mut outputs = Vec::new();
                            for ((output, rec), body) in
                                sig.outputs.iter().zip(recursive).zip(bodies)
                            {
                                let body = rename_calls(&body, &group_names);
                                outputs.push(RecDef {
                                    def: SpecDef {
                                        function: rec.clone(),
                                        params: params.clone(),
                                        guard: guard.clone(),
                                        body,
                                    },
                                    type_guard: type_guard.clone(),
                                    // Trait implementations inherit public
                                    // typing, but do not emit `pre_post_rec`.
                                    return_predicate: if decl.attrs.is_trait_method_impl || !matches!(output.leaf, LeafTy::Poly(_)) { None } else {
                                        match ctx.type_fact(output.leaf, &reads.types, &Term::var("result_value", output.leaf.sort()), decl.span) {
                                            Ok(predicate) => Some(predicate),
                                            Err(problem) => { problems.insert(decl.id, problem); continue 'bodies; }
                                        }
                                    },
                                    return_bounds: (!decl.attrs.is_trait_method_impl
                                        && matches!(output.leaf, LeafTy::Int(range) if range != IntRange::Int))
                                        .then(|| output.leaf.bounds()),
                                    spec_name: output.name.clone(),
                                    cycle,
                                    sort: output.leaf.sort(),
                                });
                            }
                            rec_defs.insert(decl.id, outputs);
                        }
                        _ => {
                            defs.insert(
                                decl.id,
                                sig.outputs
                                    .iter()
                                    .zip(bodies)
                                    .map(|(output, body)| SpecDef {
                                        function: output.name.clone(),
                                        params: params.clone(),
                                        guard: guard.clone(),
                                        body,
                                    })
                                    .collect(),
                            );
                        }
                    }
                }
                // Uninterpreted: the calls stay applications.
                Body::None => {}
                Body::Stmts(block) => {
                    let span = block.stmts.first().map_or(decl.span, |stmt| stmt.span);
                    problems.insert(
                        decl.id,
                        refusal("vcgen-internal", "a spec function with statements", span),
                    );
                }
            }
        }

        // Circular definitions outside the declared groups: a function on a
        // cycle with a function that is not a member of its group.
        for decl in &spec_fns {
            let circular = spec_fns.iter().any(|other| {
                !ctx.same_group(decl.id, other.id)
                    && reaches(&callees, decl.id, other.id)
                    && reaches(&callees, other.id, decl.id)
            });
            if circular {
                problems.entry(decl.id).or_insert_with(|| {
                    refusal(
                        "recursive-spec-fn",
                        format!(
                            "`{}` is recursive outside a group of recursive functions",
                            decl.name
                        ),
                        decl.span,
                    )
                });
            }
        }
        // Dependence on a refused definition, to a fixpoint.
        loop {
            let mut changed = false;
            for decl in &spec_fns {
                if problems.contains_key(&decl.id) {
                    continue;
                }
                let failed = callees.get(&decl.id).and_then(|called| {
                    called
                        .iter()
                        .find_map(|callee| problems.get(callee).cloned())
                });
                if let Some(problem) = failed {
                    problems.insert(decl.id, problem);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        for (id, problem) in problems {
            defs.remove(&id);
            rec_defs.remove(&id);
            if let Some(sig) = sigs.get_mut(&id) {
                sig.problem.get_or_insert(problem);
            }
        }

        let rec_names = rec_defs
            .iter()
            .flat_map(|(id, outputs)| {
                outputs
                    .iter()
                    .enumerate()
                    .map(move |(leaf, rec)| (rec.def.function.clone(), (*id, leaf)))
            })
            .collect();
        Self {
            sigs,
            defs,
            rec_defs,
            rec_names,
            functions,
            families,
            ranged,
            typings,
        }
    }

    /// The recursive spec function whose fixpoint function is `name`
    /// (`rf<i>`), if any.
    pub(crate) fn rec_def_named(&self, name: &str) -> Option<&RecDef> {
        let (id, leaf) = self.rec_names.get(name)?;
        self.rec_defs.get(id)?.get(*leaf)
    }
}

/// Parameter typing invariants over the flattened definition parameters.
fn parameter_types(ctx: &Ctx<'_>, sig: &SpecSig, env: &TypeEnv, params: &[Val]) -> R<Term> {
    let mut facts = Vec::new();
    for (shape, value) in sig.params.iter().zip(params) {
        let mut leaves = Vec::new();
        shape.leaves(&mut leaves);
        let mut terms = Vec::new();
        value.leaves(&mut terms);
        for (leaf, term) in leaves.iter().zip(&terms) {
            facts.push(ctx.type_fact(*leaf, env, term, crate::SpanId(0))?);
        }
    }
    Ok(Term::and(facts))
}

/// Verus's `def_reqs`: parameter typing and `decreases_when`, whereas the
/// recursive return-type invariant uses parameter typing alone.
fn def_reqs(tr: &mut Tr<'_>, type_guard: &Term, decl: &FnDecl) -> R<Term> {
    let mut facts = vec![type_guard.clone()];
    if let Some(when) = &decl.decreases_when {
        facts.push(tr.bool(when)?);
    }
    Ok(Term::and(facts))
}

#[cfg(all(test, feature = "solve"))]
mod recursive_result_types_tests;

/// `term` with the calls of the functions named in `names` renamed.
fn rename_calls(term: &Term, names: &HashMap<&str, &str>) -> Term {
    let renamed: Result<Term, ()> = term.map_calls(&mut |name, args, sort| {
        Ok(Term::call(
            names.get(name).copied().unwrap_or(name),
            args,
            sort,
        ))
    });
    renamed.unwrap_or_else(|()| term.clone())
}

/// The signature and complete result layout of spec function number `index`.
fn signature(ctx: &Ctx<'_>, decl: &FnDecl, index: usize) -> SpecSig {
    let mut sig = SpecSig {
        owner: decl.id,
        boxed_params: !decl.type_params.is_empty(),
        n_types: decl.type_params.len(),
        params: Vec::new(),
        result: Shape::Node(Vec::new()),
        outputs: Vec::new(),
        problem: None,
    };
    if let Some(problem) = decl.imported_problem() {
        sig.problem = Some(refusal("imported-declaration", problem, decl.span));
        return sig;
    }
    if decl.role == FnRole::Imported && ctx.group(decl.id).is_some() {
        sig.problem = Some(refusal(
            "imported-declaration",
            "an imported recursive declaration",
            decl.span,
        ));
        return sig;
    }
    for param in &decl.params {
        let Some(local) = decl.local(*param) else {
            sig.problem = Some(refusal("vcgen-internal", "a missing parameter", decl.span));
            return sig;
        };
        match if sig.boxed_params {
            ctx.poly_shape(&local.ty, Some(decl.id), local.span)
        } else {
            ctx.shape(&local.ty, Some(decl.id), local.span)
        } {
            Ok(shape) => sig.params.push(shape),
            Err(problem) => {
                sig.problem = Some(problem);
                return sig;
            }
        }
    }
    let ret_ty = decl.ret_ty().cloned().unwrap_or(crate::Ty::Unit);
    match ctx.shape(&ret_ty, Some(decl.id), decl.span) {
        Ok(result) => {
            let mut leaves = Vec::new();
            result.leaves(&mut leaves);
            sig.outputs = leaves
                .into_iter()
                .enumerate()
                .map(|(leaf, ty)| SpecOutput {
                    name: result_name("sf", index, &result, leaf),
                    leaf: ty,
                })
                .collect();
            sig.result = result;
        }
        Err(problem) => sig.problem = Some(problem),
    }
    sig
}

/// Definition parameters (`a0`, `a1`, ...) for a signature's type
/// parameters and flattened leaves, with the type terms and the parameter
/// values built from them.
fn definition_params(sig: &SpecSig) -> (TypeEnv, Vec<Val>, Vec<(String, Sort)>) {
    fn build(shape: &Shape, params: &mut Vec<(String, Sort)>) -> Val {
        match shape {
            Shape::Leaf(leaf) => {
                let name = format!("a{}", params.len());
                params.push((name.clone(), leaf.sort()));
                Val::Leaf(Term::var(name, leaf.sort()))
            }
            Shape::Node(children) => {
                Val::Node(children.iter().map(|child| build(child, params)).collect())
            }
        }
    }
    let mut params = Vec::new();
    let mut type_args = Vec::new();
    for _ in 0..sig.n_types {
        let decoration = format!("a{}", params.len());
        params.push((decoration.clone(), Sort::Decoration));
        let identity = format!("a{}", params.len());
        params.push((identity.clone(), Sort::TypeId));
        type_args.push(TypeArgument::named(decoration, identity));
    }
    let types = TypeEnv::new(sig.owner, type_args);
    let vals = sig
        .params
        .iter()
        .map(|shape| build(shape, &mut params))
        .collect();
    (types, vals, params)
}

/// Does `from` reach `to` through one or more calls?
fn reaches(callees: &HashMap<FnId, BTreeSet<FnId>>, from: FnId, to: FnId) -> bool {
    let mut stack: Vec<FnId> = callees.get(&from).into_iter().flatten().copied().collect();
    let mut seen = BTreeSet::new();
    while let Some(next) = stack.pop() {
        if next == to {
            return true;
        }
        if seen.insert(next) {
            stack.extend(callees.get(&next).into_iter().flatten().copied());
        }
    }
    false
}

/// Inline every call of a function defined in `defs` (by solver name), to a
/// fixpoint. A definition with a guard inlines as `if guard { body } else
/// { call }`. `budget` bounds the number of term nodes inlining may add;
/// `None` is returned when it runs out. The definitions are not circular
/// (see the module documentation), so inlining terminates.
pub(crate) fn inline(
    term: &Term,
    defs: &HashMap<&str, &SpecDef>,
    budget: &mut usize,
) -> Option<Term> {
    term.map_calls(&mut |name, args, sort| -> Result<Term, ()> {
        let Some(def) = defs.get(name).filter(|def| def.params.len() == args.len()) else {
            return Ok(Term::call(name, args, sort));
        };
        let cost = def.body.size().saturating_add(def.guard.size());
        *budget = budget.checked_sub(cost).ok_or(())?;
        let (guard, body) = instantiate(def, &args);
        let body = inline(&body, defs, budget).ok_or(())?;
        if guard == Term::Bool(true) {
            return Ok(body);
        }
        let guard = inline(&guard, defs, budget).ok_or(())?;
        Ok(Term::ite(guard, body, Term::call(name, args, sort)))
    })
    .ok()
}

/// The guard and body of `def` at the arguments `args`.
pub(crate) fn instantiate(def: &SpecDef, args: &[Term]) -> (Term, Term) {
    let map = def
        .params
        .iter()
        .map(|(param, _)| param.as_str())
        .zip(args.iter().cloned())
        .collect();
    (def.guard.substitute(&map), def.body.substitute(&map))
}

/// The recursive spec functions a query may unfold: each revealed member
/// whose definition Verus has emitted, by its solver name (`sf<i>`), with
/// the number of times a call of it unfolds along a chain (its cycle
/// length plus its fuel, less one).
pub(crate) type Unfoldable<'t> = HashMap<&'t str, (&'t RecDef, u32)>;

/// The facts Verus's fuel gives about the recursive spec functions, from
/// the applications `seeds` of unfoldable functions with the conditions
/// under which Z3 has them relevant (`super::relevance`).
///
/// Every node of the unfolding has a relevance symbol, true where some
/// path to the node is: a seed's condition, a call's symbol for its own
/// fixpoint application, or a parent's symbol, guard and the condition of
/// the application in the parent's body. The symbols are written out
/// where their definitions are small (`Namer::resolve`). A call
/// `sf<i>(x)` gives `rel ==> (guard(x) ==> sf<i>(x) == rf<i>(x))`, and an
/// application `rf<j>(y)` reached with fuel left gives `rel ==> (guard(y)
/// ==> rf<j>(y) == body(y))`, where the body's recursive calls have one
/// unit of fuel less (Verus's `fuel_to_body` axiom, which Z3 instantiates
/// on a relevant `rec%f(y, succ fuel)`). The facts are inlined with `defs`;
/// the symbols and their definitions go to `analysis`'s namer. `None` when
/// a budget runs out.
pub(crate) fn unfold(
    seeds: Vec<(Term, Term)>,
    unfoldable: &Unfoldable<'_>,
    tables: &Tables,
    defs: &HashMap<&str, &SpecDef>,
    analysis: &mut Analysis<'_>,
    budget: &mut usize,
) -> Option<Vec<Term>> {
    /// An unfolding: a call of an unfoldable function, or a fixpoint
    /// application with the fuel it has.
    #[derive(Clone, PartialEq, Eq, Hash)]
    enum Key {
        Link(FnId, Vec<Term>),
        Unfold(FnId, Vec<Term>, u32),
    }
    struct Nodes {
        index: HashMap<Key, usize>,
        list: Vec<(Key, Term, Vec<Term>)>,
    }
    impl Nodes {
        fn reach(&mut self, key: Key, cond: Term, analysis: &mut Analysis<'_>) {
            if cond == Term::Bool(false) {
                return;
            }
            if let Some(&i) = self.index.get(&key) {
                self.list[i].2.push(cond);
            } else {
                self.index.insert(key.clone(), self.list.len());
                self.list.push((key, analysis.namer.fresh(), vec![cond]));
            }
        }
    }

    let inline_all = |terms: &[Term], budget: &mut usize| -> Option<Vec<Term>> {
        terms.iter().map(|t| inline(t, defs, budget)).collect()
    };
    let mut nodes = Nodes {
        index: HashMap::new(),
        list: Vec::new(),
    };
    for (call, cond) in seeds {
        if let Term::Call { name, args, .. } = call {
            if let Some((rec, _)) = unfoldable.get(name.as_str()) {
                let args = inline_all(&args, budget)?;
                let (id, _) = tables.rec_names.get(&rec.def.function)?;
                nodes.reach(Key::Link(*id, args), cond, analysis);
            }
        }
    }
    let mut facts: Vec<Term> = Vec::new();
    // The instance of each fixpoint application, and the symbols of the
    // nodes that make it.
    let mut instances: Vec<(Term, Vec<Term>)> = Vec::new();
    let mut instance_index: HashMap<(String, Vec<Term>), usize> = HashMap::new();
    let mut next = 0;
    while next < nodes.list.len() {
        let (key, symbol, _) = nodes.list[next].clone();
        next += 1;
        match key {
            Key::Link(id, args) => {
                let family = tables.rec_defs.get(&id)?;
                let first = family.first()?;
                let (_, depth) = *unfoldable.get(first.spec_name.as_str())?;
                let (guard, _) = instantiate(&first.def, &args);
                let guard = inline(&guard, defs, budget)?;
                for rec in family {
                    *budget = budget.checked_sub(rec.def.guard.size().saturating_add(1))?;
                    let (_, member_depth) = *unfoldable.get(rec.spec_name.as_str())?;
                    if member_depth != depth
                        || rec.def.params != first.def.params
                        || rec.def.guard != first.def.guard
                    {
                        return None;
                    }
                    let call = Term::call(rec.spec_name.clone(), args.clone(), rec.sort);
                    let fixpoint = Term::call(rec.def.function.clone(), args.clone(), rec.sort);
                    let fact = Term::implies(
                        symbol.clone(),
                        Term::implies(guard.clone(), Term::eq(call, fixpoint)),
                    );
                    facts.push(fact);
                }
                // The bridge exposes the fixpoint only where its guard
                // holds. A type fact must not introduce a helper application
                // that the guarded bridge never made relevant.
                let key = Key::Unfold(id, args, depth);
                nodes.reach(key, Term::and([symbol, guard]), analysis);
            }
            Key::Unfold(id, args, fuel) => {
                // One recursive application returns the whole value. Its
                // component equations share relevance and fuel, including
                // components another observation reaches at zero fuel.
                for rec in tables.rec_defs.get(&id)? {
                    let name = &rec.def.function;
                    if let Some(predicate) = &rec.return_predicate {
                        let mut params: HashMap<&str, Term> = rec
                            .def
                            .params
                            .iter()
                            .map(|(name, _)| name.as_str())
                            .zip(args.iter().cloned())
                            .collect();
                        params.insert(
                            "result_value",
                            Term::call(name.clone(), args.clone(), rec.sort),
                        );
                        let fact = Term::implies(
                            symbol.clone(),
                            Term::implies(
                                rec.type_guard.substitute(&params),
                                predicate.substitute(&params),
                            ),
                        );
                        *budget = budget.checked_sub(fact.size())?;
                        facts.push(fact);
                    }
                    if let Some((lo, hi)) = rec.return_bounds {
                        let params = rec
                            .def
                            .params
                            .iter()
                            .map(|(name, _)| name.as_str())
                            .zip(args.iter().cloned())
                            .collect();
                        let guard = rec.type_guard.substitute(&params);
                        let app = Term::call(name.clone(), args.clone(), rec.sort);
                        // `pre_post_rec` is independent of the body/fuel axiom:
                        // it needs typed arguments, not `decreases_when` or
                        // positive fuel. Keep the application's relevance guard.
                        let fact = Term::implies(
                            symbol.clone(),
                            Term::implies(guard, app.within_type_bounds(lo, hi)),
                        );
                        *budget = budget.checked_sub(fact.size())?;
                        facts.push(fact);
                    }
                    if fuel == 0 {
                        continue;
                    }
                    let cost = rec.def.body.size().saturating_add(rec.def.guard.size());
                    *budget = budget.checked_sub(cost)?;
                    let (guard, body) = instantiate(&rec.def, &args);
                    let guard = inline(&guard, defs, budget)?;
                    let instance_key = (name.clone(), args.clone());
                    if let Some(&i) = instance_index.get(&instance_key) {
                        instances[i].1.push(symbol.clone());
                    } else {
                        let inlined = inline(&body, defs, budget)?;
                        let app = Term::call(name.clone(), args.clone(), rec.sort);
                        let fact = Term::implies(guard.clone(), Term::eq(app, inlined));
                        instance_index.insert(instance_key, instances.len());
                        instances.push((fact, vec![symbol.clone()]));
                    }
                    let calls = analysis.body(&body).ok()?;
                    let gate = if calls.is_empty() {
                        Term::Bool(true)
                    } else {
                        analysis.gate(&rec.def, &args)
                    };
                    for (call, cond) in calls.into_items() {
                        let Term::Call {
                            name: callee,
                            args: callee_args,
                            ..
                        } = call
                        else {
                            continue;
                        };
                        let cond = Term::and([symbol.clone(), guard.clone(), gate.clone(), cond]);
                        let callee_args = inline_all(&callee_args, budget)?;
                        if let Some((callee_id, _)) = tables.rec_names.get(&callee) {
                            let key = Key::Unfold(*callee_id, callee_args, fuel - 1);
                            nodes.reach(key, cond, analysis);
                        } else if let Some((member, _)) = unfoldable.get(callee.as_str()) {
                            let (callee_id, _) = tables.rec_names.get(&member.def.function)?;
                            nodes.reach(Key::Link(*callee_id, callee_args), cond, analysis);
                        }
                    }
                }
            }
        }
    }
    for (fact, symbols) in instances {
        facts.push(Term::implies(Term::or(symbols), fact));
    }
    for (_, symbol, conds) in nodes.list {
        analysis.namer.define(&symbol, Term::or(conds));
    }
    Some(facts)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clip_keeps_values_in_range() {
        let x = Term::var("x", Sort::Int);
        let text = clip(IntRange::U(8), x).to_string();
        assert_eq!(text, "(ite (and (<= 0 x) (<= x 255)) x (clip_u8_oob x))");
        assert_eq!(clip(IntRange::U(8), Term::Int(7)), Term::Int(7));
        let over = clip(IntRange::I(8), Term::Int(200)).to_string();
        assert_eq!(over, "(clip_i8_oob 200)");
    }

    #[test]
    fn inlining_substitutes_and_stops() {
        let body = Term::arith(
            super::super::term::ArithOp::Add,
            Term::var("a0", Sort::Int),
            Term::Int(1),
        );
        let def = SpecDef {
            function: "sf0".to_string(),
            params: vec![("a0".to_string(), Sort::Int)],
            guard: Term::Bool(true),
            body,
        };
        let defs = HashMap::from([("sf0", &def)]);
        let call = Term::call("sf0", vec![Term::var("v0", Sort::Int)], Sort::Int);
        let mut budget = 100;
        let inlined = inline(&call, &defs, &mut budget).unwrap();
        assert_eq!(inlined.to_string(), "(+ v0 1)");
        let mut budget = 1;
        assert!(inline(&call, &defs, &mut budget).is_none());
    }
}
