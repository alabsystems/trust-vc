// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refuses a `Verified` answer for a function that can evaluate a bodiless
//! exec function, or a parameter of a callable type, more than once.
//!
//! The lane reads a call of a function whose body it does not read as one
//! application of one function symbol, constrained only by the callee's
//! contract. Two calls with equal arguments are then the same term, so the
//! lane takes them to return the same value. That is true only for a
//! function of its arguments. A bodiless exec function (`#[external_body]`,
//! `#[external]`, or any function inside an `impl`, `mod` or `trait` carrying
//! one of those markers) may read a counter, a clock or an input. Under
//! `#[ensures(result < 100u64)] fn read_input() -> u64`, the symbol model
//! proves `read_input() - read_input()` free of underflow and `a == b` for
//! `let a = read_input(); let b = read_input();`, and both are false at run
//! time for a body that returns 0 and then 50.
//!
//! One evaluation is one term, which is sound. So this module counts, for the
//! function being verified, the places that can put a term of such a
//! function (a "root") into its query:
//!
//! * every mention of the root's name in the function's body and contract,
//!   in a call, a method call, a path, or the tokens of a macro or attribute;
//! * every mention in the body and contract of each function of the file it
//!   mentions, transitively, since the lane can publish a callee's body as a
//!   definitional axiom (`fn wrap() -> u64 { read_input() }` makes `wrap()`
//!   and `read_input()` one term) and reads a callee's contract at the call.
//!
//! The answer is refused when a root can be evaluated twice: a root counted
//! twice, a mention of a function that reaches a root inside a loop or a
//! closure (evaluated once per iteration or per call), or a function that
//! reaches a root and reaches itself (evaluated once per recursion level).
//!
//! The count reads names as text, so it over-counts: a std method or a local
//! variable spelled like a root counts as a mention of it, same-named
//! functions are all expanded, and a `use .. as ..` rename counts as a
//! mention of what it renames. Over-counting only refuses more.
//!
//! An operator, comparison, `for` loop, `?`, dereference or format call
//! invokes a trait method without naming it. When a method of an impl of
//! such a trait reaches a root, every function of the file is refused.
//!
//! A parameter of a callable type (`f: F` with `F: Fn(u64) -> u64`, `impl
//! Fn()`, `&dyn Fn()`, a `fn` pointer) is read the same way: a call `f(x)` is
//! one application of one function symbol. An `Fn` closure can still read
//! shared state (an atomic, a `Cell` it borrows, a `static`), so two calls
//! with equal arguments can return different values. The answer is refused
//! when the function mentions such a parameter twice, or once inside a loop
//! or a closure, in its body or contract. The reflection predicates
//! `f.requires(..)` and `f.ensures(..)` do not call `f` and are not counted.
//! A function of the file that evaluates one of its own callable parameters
//! more than once is treated like a root that is already evaluated twice:
//! any function that reaches it is refused, because the lane can publish its
//! body as a definitional axiom.
//!
//! A method called on a value of a generic type (`t.read()` with `t: &T` and
//! `T: Tr`, `impl Tr`, `dyn Tr`, `self` in a trait) and a path call on a
//! generic type (`T::make()`, `<T as Tr>::make()`, `Tr::read(&t)`) run an
//! impl the caller chooses, and the lane reads them as one function symbol
//! of the receiver and arguments. Such a call is a root under the name of
//! its method, counted like the roots above (see [`super::generic_values`]
//! for which values count as generic). A method the file declares only as a
//! spec function is not a root.
//!
//! A comparison of values of a generic type in executable code (`x == y`,
//! `x != y`, `x < y`, `assert_eq!(x, y)`, `x.eq(&y)`, `v.contains(&x)` with
//! `x: T`) runs the type's own `PartialEq` or `PartialOrd` impl, which the
//! lane reads as structural equality or fails to read. Structural equality
//! is reflexive and stable, and an impl need not be either: `f64::NAN ==
//! f64::NAN` is false, and an `eq` that reads a `Cell` another call changed
//! gives a new answer. One such comparison refuses the answer, and so does
//! reaching a function of the file whose executable body has one, or a
//! method of an operator or comparison impl of the file whose body has one.
//! The same holds for a comparison of values of a type whose impl the file
//! does not show (a type another file or crate declares, or one of the
//! file's types that another file can implement it for; see
//! [`super::runtime_checked_clauses::opaque_type_names`]): the lane reads
//! it as structural equality, and the impl it runs is not read.
//! A comparison in a contract, a spec or proof function or a proof macro is
//! spec equality, which is structural, and is not refused, except in a
//! clause of an exec function that the `trust_vc` macros check at run time
//! outside a verification build: that check runs the impl. There a
//! comparison of values of a generic type, or of a type whose impl the file
//! does not show, refuses the function's answer (see
//! [`super::runtime_checked_clauses`]), and one in a precondition also
//! refuses every function that reaches it, since the lane reads the
//! comparison where the precondition is established.
//!
//! Not covered: a spec function is a function of its arguments by
//! declaration, and a `const fn` cannot read mutable state, so neither is a
//! root. A root that returns `()` has one value, so it is not a root either.
//! A function's own `&mut` outputs are fresh symbols at each call, so they
//! are not affected.

use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{File, ItemFn, Token};

use super::attr_extract::has_external_trusted_attr;
use super::generic_values::{
    is_comparison, type_kind, type_param_names, FileDecls, GenericScope, Kind, OuterContext,
};
use super::runtime_checked_clauses::{
    checked_attribute_clauses, checked_macro_clause, compares_opaque_values, names_any,
    opaque_type_names, opaque_value_names, CheckedClause,
};

/// Leading text of every refusal this module produces for a repeated
/// evaluation.
pub(super) const BODILESS_CALL_REPEAT_TAG: &str = "bodiless call repeated";

/// Leading text of the refusal for a comparison of values of a generic type.
pub(super) const GENERIC_COMPARISON_TAG: &str = "generic comparison";

/// Leading text of the refusal for a comparison in executable code of values
/// of a type whose impl the file does not show.
pub(super) const FOREIGN_COMPARISON_TAG: &str = "foreign comparison";

/// Leading text of the refusal for a comparison in a clause the `trust_vc`
/// macros check at run time.
pub(super) const CHECKED_COMPARISON_TAG: &str = "run-time checked comparison";

/// Prefix of the root name a method call on a value of a generic type counts
/// under. It is not an identifier, so it cannot collide with a file name.
const GENERIC_METHOD_PREFIX: &str = "<generic>::";

/// Separates the method from the receiver's generic type in a root name.
const RECEIVER_TYPE_SEPARATOR: char = '@';

/// Methods that compare their receiver with their arguments through
/// `PartialEq`, `PartialOrd` or `Ord`.
const COMPARISON_METHODS: &[&str] = &[
    "eq",
    "ne",
    "lt",
    "le",
    "gt",
    "ge",
    "cmp",
    "partial_cmp",
    "max",
    "min",
    "clamp",
];

/// Collection methods that compare an argument with the elements through
/// `PartialEq` or `Ord`.
const ELEMENT_COMPARISON_METHODS: &[&str] = &[
    "contains",
    "starts_with",
    "ends_with",
    "binary_search",
    "strip_prefix",
    "strip_suffix",
];

/// Std macros that compare their first two arguments with `==`.
const COMPARISON_MACROS: &[&str] = &[
    "assert_eq",
    "assert_ne",
    "debug_assert_eq",
    "debug_assert_ne",
];

/// Macros that hold spec or proof code, whatever their path. A macro spelled
/// with a `trust_vc`, `vstd` or `builtin` path is spec code too; a bare
/// `assert!` is std's runtime assertion.
const SPEC_MACROS: &[&str] = &[
    "proof",
    "proof_block",
    "ghost",
    "calc",
    "assume",
    "assert_by",
    "assert_forall_by",
    "assert_by_contradiction",
    "assert_with_proof",
    "assert_by_nonlinear",
    "assert_by_bit_vector",
    "assert_by_compute",
    "assert_seqs_equal",
    "invariant",
    "invariant_except_break",
    "loop_ensures",
    "loop_decreases",
    "decreases_to",
    "forall",
    "exists",
    "choose",
    "old",
    "requires",
    "ensures",
    "recommends",
    "ext_eq",
    "ext_ne",
    "equal",
    "strict_eq",
];

/// Roots of spec and proof paths.
const SPEC_MACRO_ROOTS: &[&str] = &["trust_vc", "vstd", "builtin", "verus_builtin"];

/// Traits whose methods are invoked by syntax that does not name the method.
pub(super) const IMPLICIT_CALL_TRAITS: &[&str] = &[
    "Add",
    "Sub",
    "Mul",
    "Div",
    "Rem",
    "Neg",
    "Not",
    "BitAnd",
    "BitOr",
    "BitXor",
    "Shl",
    "Shr",
    "AddAssign",
    "SubAssign",
    "MulAssign",
    "DivAssign",
    "RemAssign",
    "BitAndAssign",
    "BitOrAssign",
    "BitXorAssign",
    "ShlAssign",
    "ShrAssign",
    "Index",
    "IndexMut",
    "Deref",
    "DerefMut",
    "PartialEq",
    "Eq",
    "PartialOrd",
    "Ord",
    "Iterator",
    "IntoIterator",
    "DoubleEndedIterator",
    "From",
    "Into",
    "TryFrom",
    "TryInto",
    "FromResidual",
    "Try",
    "Display",
    "Debug",
    "Drop",
    "Fn",
    "FnMut",
    "FnOnce",
    "Future",
    "IntoFuture",
    "Hash",
];

/// One mention of a name in a body, a contract, or the tokens of a macro or
/// attribute.
#[derive(Clone)]
struct Mention {
    name: String,
    /// Inside a loop or a closure, so evaluated any number of times.
    repeated: bool,
}

/// Identifiers that make a type callable when they appear in it.
const CALLABLE_TYPE_IDENTS: &[&str] = &["Fn", "FnMut", "FnOnce", "fn"];

/// One function, method or trait method of the file.
struct Entry {
    name: String,
    is_root: bool,
    /// A method of an impl of an [`IMPLICIT_CALL_TRAITS`] trait.
    implicit: bool,
    /// The generic parameters of the enclosing `impl` or `trait` that are
    /// callable.
    outer_callable_types: BTreeSet<String>,
    /// The generic parameters of the enclosing `impl` or `trait`, and the
    /// kind of `Self` there.
    outer: OuterContext,
    /// The signature and body as text, which tells same-named entries apart.
    source: String,
    /// Evaluates one of its own callable parameters more than once.
    repeats_callable_param: bool,
    /// A comparison of values of a generic type in its executable body.
    generic_comparison: Option<String>,
    /// A comparison of values of a type whose impl the file does not show
    /// in its executable body.
    foreign_comparison: Option<String>,
    /// A comparison, in a precondition the `trust_vc` macros check at run
    /// time, of values of a generic type or of a type whose impl the file
    /// does not show.
    checked_precondition: Option<String>,
    mentions: Vec<Mention>,
}

/// The refusal message for a `Verified` answer of `func`, or `None` when
/// `func` evaluates every bodiless exec function and every callable
/// parameter at most once.
pub(super) fn verified_refusal(file: Option<&File>, func: &ItemFn) -> Option<String> {
    let decls = FileDecls::new(file);
    let clause_inputs = ClauseInputs::new(file);
    let mut collector = EntryCollector::new(&decls, &clause_inputs);
    if let Some(file) = file {
        collector.visit_file(file);
    }
    let mut aliases = BTreeMap::new();
    if let Some(file) = file {
        collect_renames(&mut aliases, file);
    }
    let mut func_renames = RenameCollector::default();
    func_renames.visit_item_fn(func);
    aliases.extend(func_renames.renames);

    let entries = collector.entries;
    let func_name = unraw(&func.sig.ident);
    let outer_callable_types: BTreeSet<String> = entries
        .iter()
        .filter(|entry| entry.name == func_name)
        .flat_map(|entry| entry.outer_callable_types.iter().cloned())
        .collect();
    // The enclosing context of the entry that is `func` itself, or of every
    // same-named entry when none has its exact source.
    let func_source = fn_source(&func.sig, Some(&func.block));
    let same_name: Vec<&Entry> = entries
        .iter()
        .filter(|entry| entry.name == func_name)
        .collect();
    let exact: Vec<&Entry> = same_name
        .iter()
        .copied()
        .filter(|entry| entry.source == func_source)
        .collect();
    let mut outer = OuterContext::default();
    for entry in if exact.is_empty() { &same_name } else { &exact } {
        outer.merge(&entry.outer);
    }
    let scope = GenericScope::new(&decls, &outer, &func.sig, Some(&func.block));
    let own_scan = fn_mentions(
        &func.attrs,
        &func.sig,
        Some(&func.block),
        scope.as_ref(),
        &decls,
        is_exec(&func.attrs),
        ClauseContext::new(&clause_inputs, &outer, &func.sig, Some(&func.block)),
    );
    let own_raw = own_scan.mentions;
    let params = callable_params(&func.sig, &outer_callable_types);
    if let Some(param) = repeated_callable_param(&params, &own_raw) {
        return Some(message(
            &param,
            "is a parameter of a callable type, and this function evaluates it more than once, \
             or inside a loop or a closure",
        ));
    }
    if let Some(site) = own_scan.comparison {
        return Some(comparison_message(&format!(
            "{site} is in the executable code of this function"
        )));
    }
    if let Some(site) = own_scan.foreign_comparison {
        return Some(foreign_comparison_message(&format!(
            "{site} is in the executable code of this function and compares values of a type \
             whose impl this file does not show"
        )));
    }
    if let Some(site) = own_scan.checked_comparison {
        return Some(checked_comparison_message(&format!(
            "{site}, a contract clause or assertion of this function, compares values"
        )));
    }

    let mut graph: BTreeMap<String, Vec<Mention>> = BTreeMap::new();
    for entry in &entries {
        let mentions = graph.entry(entry.name.clone()).or_default();
        for mention in &entry.mentions {
            push_resolved(mentions, mention, &aliases);
        }
    }
    let mut own = Vec::new();
    for mention in &own_raw {
        push_resolved(&mut own, mention, &aliases);
    }

    let repeaters: BTreeSet<String> = entries
        .iter()
        .filter(|entry| entry.repeats_callable_param)
        .map(|entry| entry.name.clone())
        .collect();
    if !repeaters.is_empty() {
        let reaching = root_reaching(&graph, &repeaters);
        if let Some(mention) = own.iter().find(|mention| reaching.contains(&mention.name)) {
            return Some(message(
                &mention.name,
                "reaches a function of this file that evaluates one of its own callable \
                 parameters more than once",
            ));
        }
    }

    let checkers: BTreeSet<String> = entries
        .iter()
        .filter(|entry| entry.checked_precondition.is_some())
        .map(|entry| entry.name.clone())
        .collect();
    if !checkers.is_empty() {
        let reaching = root_reaching(&graph, &checkers);
        if let Some(entry) = entries
            .iter()
            .find(|entry| entry.implicit && reaching.contains(&entry.name))
        {
            return Some(checked_comparison_message(&format!(
                "`{}` is a method of an impl of a trait that operators, comparisons, `for`, `?`, \
                 dereferences or formatting invoke without naming it, and it reaches a function \
                 whose precondition compares values",
                entry.name
            )));
        }
        if let Some(mention) = own.iter().find(|mention| reaching.contains(&mention.name)) {
            return Some(checked_comparison_message(&format!(
                "`{}` reaches a function of this file whose precondition, which this lane reads \
                 where it is established, compares values",
                mention.name
            )));
        }
    }

    type ComparisonReading = (fn(&Entry) -> bool, &'static str, fn(&str) -> String);
    let readings: [ComparisonReading; 2] = [
        (
            |entry| entry.generic_comparison.is_some(),
            "a generic type",
            comparison_message,
        ),
        (
            |entry| entry.foreign_comparison.is_some(),
            "a type whose impl this file does not show",
            foreign_comparison_message,
        ),
    ];
    for (compares, values, refusal) in readings {
        let comparers: BTreeSet<String> = entries
            .iter()
            .filter(|entry| compares(entry))
            .map(|entry| entry.name.clone())
            .collect();
        if comparers.is_empty() {
            continue;
        }
        let reaching = root_reaching(&graph, &comparers);
        if let Some(entry) = entries
            .iter()
            .find(|entry| entry.implicit && reaching.contains(&entry.name))
        {
            return Some(refusal(&format!(
                "`{}` is a method of an impl of a trait that operators, comparisons, `for`, `?`, \
                 dereferences or formatting invoke without naming it, and it reaches a function \
                 whose executable code compares values of {values}",
                entry.name
            )));
        }
        if let Some(mention) = own.iter().find(|mention| reaching.contains(&mention.name)) {
            return Some(refusal(&format!(
                "`{}` reaches a function of this file whose executable code compares values of \
                 {values}",
                mention.name
            )));
        }
    }

    let roots: BTreeSet<String> = entries
        .iter()
        .filter(|entry| entry.is_root)
        .map(|entry| entry.name.clone())
        .chain(
            own.iter()
                .chain(graph.values().flatten())
                .filter(|mention| mention.name.starts_with(GENERIC_METHOD_PREFIX))
                .map(|mention| mention.name.clone()),
        )
        .collect();
    if roots.is_empty() {
        return None;
    }
    let reaching = root_reaching(&graph, &roots);

    if let Some(entry) = entries
        .iter()
        .find(|entry| entry.implicit && reaching.contains(&entry.name))
    {
        return Some(message(
            &entry.name,
            "is a method of an impl of a trait that operators, comparisons, `for`, `?`, \
             dereferences or formatting invoke without naming it, and it reaches a function \
             whose body this lane does not read",
        ));
    }

    if let Some(mention) = own
        .iter()
        .find(|mention| mention.repeated && reaching.contains(&mention.name))
    {
        return Some(message(
            &mention.name,
            "is evaluated inside a loop or a closure of this function and reaches a function \
             whose body this lane does not read",
        ));
    }

    let mut reached = BTreeSet::new();
    let mut pending: Vec<String> = own
        .iter()
        .filter(|mention| graph.contains_key(&mention.name))
        .map(|mention| mention.name.clone())
        .collect();
    while let Some(name) = pending.pop() {
        if !reached.insert(name.clone()) {
            continue;
        }
        for mention in graph.get(&name).into_iter().flatten() {
            if graph.contains_key(&mention.name) && !reached.contains(&mention.name) {
                pending.push(mention.name.clone());
            }
        }
    }
    for name in &reached {
        for mention in graph.get(name).into_iter().flatten() {
            if mention.repeated && reaching.contains(&mention.name) {
                return Some(message(
                    &mention.name,
                    &format!(
                        "is evaluated inside a loop or a closure of `{name}`, which this function \
                         reaches, and reaches a function whose body this lane does not read"
                    ),
                ));
            }
        }
        if reaching.contains(name) && reaches_itself(&graph, name) {
            return Some(message(
                name,
                "is recursive, which this function reaches, and reaches a function whose body \
                 this lane does not read",
            ));
        }
    }

    let mut memo = BTreeMap::new();
    let mut stack = BTreeSet::new();
    let mut counts = BTreeMap::new();
    for mention in &own {
        add_mention(&mut counts, mention, &graph, &roots, &mut memo, &mut stack);
    }
    let root = repeated_root(&counts)?;
    Some(message(
        &root,
        "can be evaluated more than once by this function, directly or through the body or \
         contract of a function it calls",
    ))
}

/// A root `counts` shows evaluated twice. A method of a generic value is
/// counted per receiver type when its receiver is a parameter of a generic
/// type (`<generic>::read@T`), and under the bare method name otherwise. Two
/// parameters of different generic types are never the same value, so their
/// counts are kept apart; a call whose receiver is anything else may be on
/// either, so it adds to all of them.
fn repeated_root(counts: &BTreeMap<String, u8>) -> Option<String> {
    let mut methods: BTreeMap<&str, (u8, u8, u8)> = BTreeMap::new();
    for (name, count) in counts {
        let Some(rest) = name.strip_prefix(GENERIC_METHOD_PREFIX) else {
            if *count >= 2 {
                return Some(name.clone());
            }
            continue;
        };
        match rest.split_once(RECEIVER_TYPE_SEPARATOR) {
            None => {
                let entry = methods.entry(rest).or_default();
                entry.0 = entry.0.saturating_add(*count);
            }
            Some((method, _)) => {
                let entry = methods.entry(method).or_default();
                entry.1 = entry.1.saturating_add(*count);
                entry.2 = entry.2.max(*count);
            }
        }
    }
    methods
        .into_iter()
        .find(|(_, (untyped, typed, most))| {
            *untyped >= 2 || (*untyped >= 1 && *typed >= 1) || *most >= 2
        })
        .map(|(method, _)| format!("{GENERIC_METHOD_PREFIX}{method}"))
}

fn message(name: &str, why: &str) -> String {
    let subject = match name.strip_prefix(GENERIC_METHOD_PREFIX) {
        Some(method) => format!(
            "`{}`, called on a value of a generic type whose impl this lane does not see,",
            method
                .split_once(RECEIVER_TYPE_SEPARATOR)
                .map_or(method, |(method, _)| method)
        ),
        None => format!("`{name}`"),
    };
    format!(
        "{BODILESS_CALL_REPEAT_TAG}: {subject} {why}. The lane reads every call of such a \
         function with the same arguments as the same value, which holds only for a function of \
         its arguments, so a `Verified` answer is refused; a refutation would be kept"
    )
}

fn checked_comparison_message(why: &str) -> String {
    format!(
        "{CHECKED_COMPARISON_TAG}: {why} of a generic type or of a type whose impl this file \
         does not show. Outside a verification build the `trust_vc` macros check that clause \
         with `assert!`, which runs the operands' own `PartialEq` or `PartialOrd` impl (for \
         `f64`, `f64::NAN == f64::NAN` is false), while this lane reads the comparison as \
         structural, so a `Verified` answer is refused; a refutation would be kept"
    )
}

fn comparison_message(why: &str) -> String {
    format!(
        "{GENERIC_COMPARISON_TAG}: {why}. It runs the type's own `PartialEq` or `PartialOrd` \
         impl, which this lane reads as structural equality or not at all, and an impl need not \
         be reflexive or stable (`f64::NAN == f64::NAN` is false), so a `Verified` answer is \
         refused; a refutation would be kept"
    )
}

fn foreign_comparison_message(why: &str) -> String {
    format!(
        "{FOREIGN_COMPARISON_TAG}: {why}. It runs that type's own `PartialEq` or `PartialOrd` \
         impl, which another file or crate supplies, while this lane reads the comparison as \
         structural equality, and an impl need not be reflexive or stable, so a `Verified` \
         answer is refused; a refutation would be kept"
    )
}

fn fn_source(sig: &syn::Signature, block: Option<&syn::Block>) -> String {
    let mut source = sig.to_token_stream().to_string();
    if let Some(block) = block {
        source.push_str(&block.to_token_stream().to_string());
    }
    source
}

fn is_exec(attrs: &[syn::Attribute]) -> bool {
    crate::mode_attrs::classify_attrs(attrs) == crate::mode::FunctionMode::Exec
}

/// Adds `mention` and every root its expansion evaluates to `counts`, capped
/// at 2.
fn add_mention(
    counts: &mut BTreeMap<String, u8>,
    mention: &Mention,
    graph: &BTreeMap<String, Vec<Mention>>,
    roots: &BTreeSet<String>,
    memo: &mut BTreeMap<String, BTreeMap<String, u8>>,
    stack: &mut BTreeSet<String>,
) {
    if roots.contains(&mention.name) {
        bump(counts, &mention.name, 1);
    }
    if graph.contains_key(&mention.name) {
        let expansion = expand(&mention.name, graph, roots, memo, stack);
        for (root, count) in expansion {
            bump(counts, &root, count);
        }
    }
}

/// The roots evaluated by one evaluation of `name`, capped at 2. A name
/// already being expanded contributes nothing: a recursive function that
/// reaches a root is refused before counting.
fn expand(
    name: &str,
    graph: &BTreeMap<String, Vec<Mention>>,
    roots: &BTreeSet<String>,
    memo: &mut BTreeMap<String, BTreeMap<String, u8>>,
    stack: &mut BTreeSet<String>,
) -> BTreeMap<String, u8> {
    if let Some(done) = memo.get(name) {
        return done.clone();
    }
    if !stack.insert(name.to_string()) {
        return BTreeMap::new();
    }
    let mut counts = BTreeMap::new();
    for mention in graph.get(name).into_iter().flatten() {
        add_mention(&mut counts, mention, graph, roots, memo, stack);
    }
    stack.remove(name);
    memo.insert(name.to_string(), counts.clone());
    counts
}

fn bump(counts: &mut BTreeMap<String, u8>, name: &str, by: u8) {
    let count = counts.entry(name.to_string()).or_insert(0);
    *count = count.saturating_add(by).min(2);
}

/// Every name that is a root or mentions, transitively, a root.
fn root_reaching(
    graph: &BTreeMap<String, Vec<Mention>>,
    roots: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut reaching = roots.clone();
    loop {
        let before = reaching.len();
        for (name, mentions) in graph {
            if !reaching.contains(name)
                && mentions
                    .iter()
                    .any(|mention| reaching.contains(&mention.name))
            {
                reaching.insert(name.clone());
            }
        }
        if reaching.len() == before {
            return reaching;
        }
    }
}

fn reaches_itself(graph: &BTreeMap<String, Vec<Mention>>, start: &str) -> bool {
    let mut seen = BTreeSet::new();
    let mut pending: Vec<&str> = graph
        .get(start)
        .into_iter()
        .flatten()
        .map(|mention| mention.name.as_str())
        .collect();
    while let Some(name) = pending.pop() {
        if name == start {
            return true;
        }
        if !seen.insert(name) {
            continue;
        }
        for mention in graph.get(name).into_iter().flatten() {
            pending.push(mention.name.as_str());
        }
    }
    false
}

/// Pushes `mention`, and the name it renames when it is a `use` rename.
fn push_resolved(out: &mut Vec<Mention>, mention: &Mention, aliases: &BTreeMap<String, String>) {
    out.push(mention.clone());
    let mut name = &mention.name;
    let mut seen = BTreeSet::new();
    while let Some(original) = aliases.get(name) {
        if !seen.insert(original.clone()) {
            break;
        }
        out.push(Mention {
            name: original.clone(),
            repeated: mention.repeated,
        });
        name = original;
    }
}

/// Every `use .. as ..` rename in the file, from the new name to the renamed
/// one.
fn collect_renames(aliases: &mut BTreeMap<String, String>, file: &File) {
    let mut collector = RenameCollector::default();
    collector.visit_file(file);
    aliases.extend(collector.renames);
}

#[derive(Default)]
struct RenameCollector {
    renames: BTreeMap<String, String>,
}

impl<'ast> Visit<'ast> for RenameCollector {
    fn visit_use_rename(&mut self, rename: &'ast syn::UseRename) {
        self.renames
            .insert(unraw(&rename.rename), unraw(&rename.ident));
    }
}

fn unraw(ident: &syn::Ident) -> String {
    syn::ext::IdentExt::unraw(ident).to_string()
}

/// Collects every function, method and trait method of the file, with the
/// trusted-boundary markers and the generics of its enclosing `mod`, `impl`
/// and `trait`.
struct EntryCollector<'d> {
    decls: &'d FileDecls,
    clause_inputs: &'d ClauseInputs,
    trusted: Vec<bool>,
    implicit: Vec<bool>,
    generics: Vec<syn::Generics>,
    /// The kind of `Self` in each enclosing `impl` or `trait`, and its kind
    /// with the file's opaque type names read as generic.
    self_kinds: Vec<(Kind, Kind)>,
    entries: Vec<Entry>,
}

impl<'d> EntryCollector<'d> {
    fn new(decls: &'d FileDecls, clause_inputs: &'d ClauseInputs) -> Self {
        EntryCollector {
            decls,
            clause_inputs,
            trusted: Vec::new(),
            implicit: Vec::new(),
            generics: Vec::new(),
            self_kinds: Vec::new(),
            entries: Vec::new(),
        }
    }

    fn enclosed_trusted(&self) -> bool {
        self.trusted.iter().any(|trusted| *trusted)
    }

    fn record(
        &mut self,
        attrs: &[syn::Attribute],
        sig: &syn::Signature,
        block: Option<&syn::Block>,
        implicit: bool,
    ) {
        let bodiless =
            block.is_some() && (has_external_trusted_attr(attrs) || self.enclosed_trusted());
        let is_root = bodiless
            && sig.constness.is_none()
            && returns_a_value(&sig.output)
            && crate::mode_attrs::classify_attrs(attrs) != crate::mode::FunctionMode::Spec;
        let outer_callable_types = callable_type_params(&self.generics, BTreeSet::new());
        let outer = OuterContext {
            type_params: self.generics.iter().flat_map(type_param_names).collect(),
            self_kind: self.self_kinds.last().map(|kinds| kinds.0),
            opaque_self_kind: self.self_kinds.last().map(|kinds| kinds.1),
        };
        let scope = GenericScope::new(self.decls, &outer, sig, block);
        let scan = fn_mentions(
            attrs,
            sig,
            block,
            scope.as_ref(),
            self.decls,
            is_exec(attrs),
            ClauseContext::new(self.clause_inputs, &outer, sig, block),
        );
        let generic_comparison = scan.comparison;
        let foreign_comparison = scan.foreign_comparison;
        let checked_precondition = scan.checked_precondition;
        let mut mentions = scan.mentions;
        // A receiver's generic type is the callee's own, which says nothing
        // about which of the caller's values reaches it.
        for mention in &mut mentions {
            if mention.name.starts_with(GENERIC_METHOD_PREFIX) {
                if let Some((method, _)) = mention.name.split_once(RECEIVER_TYPE_SEPARATOR) {
                    mention.name = method.to_string();
                }
            }
        }
        let repeats_callable_param =
            repeated_callable_param(&callable_params(sig, &outer_callable_types), &mentions)
                .is_some();
        self.entries.push(Entry {
            name: unraw(&sig.ident),
            is_root,
            implicit,
            outer_callable_types,
            outer,
            source: fn_source(sig, block),
            repeats_callable_param,
            generic_comparison,
            foreign_comparison,
            checked_precondition,
            mentions,
        });
    }

    /// Visits the items nested in a function body with none of the enclosing
    /// markers or generics, which do not reach them.
    fn nested<F: FnOnce(&mut Self)>(&mut self, visit: F) {
        let trusted = std::mem::take(&mut self.trusted);
        let implicit = std::mem::take(&mut self.implicit);
        let generics = std::mem::take(&mut self.generics);
        let self_kinds = std::mem::take(&mut self.self_kinds);
        visit(self);
        self.trusted = trusted;
        self.implicit = implicit;
        self.generics = generics;
        self.self_kinds = self_kinds;
    }
}

impl<'ast> Visit<'ast> for EntryCollector<'_> {
    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        self.trusted.push(has_external_trusted_attr(&module.attrs));
        self.implicit.push(false);
        let generics = std::mem::take(&mut self.generics);
        let self_kinds = std::mem::take(&mut self.self_kinds);
        syn::visit::visit_item_mod(self, module);
        self.generics = generics;
        self.self_kinds = self_kinds;
        self.implicit.pop();
        self.trusted.pop();
    }

    fn visit_item_impl(&mut self, item: &'ast syn::ItemImpl) {
        let implicit = item.trait_.as_ref().is_some_and(|(_, path, _)| {
            path.segments.last().is_some_and(|segment| {
                IMPLICIT_CALL_TRAITS.contains(&unraw(&segment.ident).as_str())
            })
        });
        self.trusted.push(has_external_trusted_attr(&item.attrs));
        self.implicit.push(implicit);
        self.generics.push(item.generics.clone());
        let params = type_param_names(&item.generics);
        let mut opaque_params = params.clone();
        opaque_params.extend(self.clause_inputs.opaque.iter().cloned());
        self.self_kinds.push((
            type_kind(&item.self_ty, &params, Kind::Concrete),
            type_kind(&item.self_ty, &opaque_params, Kind::Concrete),
        ));
        syn::visit::visit_item_impl(self, item);
        self.self_kinds.pop();
        self.generics.pop();
        self.implicit.pop();
        self.trusted.pop();
    }

    fn visit_item_trait(&mut self, item: &'ast syn::ItemTrait) {
        self.trusted.push(has_external_trusted_attr(&item.attrs));
        self.implicit.push(false);
        self.generics.push(item.generics.clone());
        self.self_kinds.push((Kind::Generic, Kind::Generic));
        syn::visit::visit_item_trait(self, item);
        self.self_kinds.pop();
        self.generics.pop();
        self.implicit.pop();
        self.trusted.pop();
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        // A function nested in another function's body is its own entry, and
        // the markers of the items around the outer function do not reach it.
        self.record(&item.attrs, &item.sig, Some(&item.block), false);
        self.nested(|collector| syn::visit::visit_item_fn(collector, item));
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        let implicit = self.implicit.last().copied().unwrap_or(false);
        self.record(&item.attrs, &item.sig, Some(&item.block), implicit);
        self.nested(|collector| syn::visit::visit_impl_item_fn(collector, item));
    }

    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        self.record(&item.attrs, &item.sig, item.default.as_ref(), false);
        self.nested(|collector| syn::visit::visit_trait_item_fn(collector, item));
    }
}

/// The generic type parameters declared by `generics` that are callable:
/// those whose bounds name `Fn`, `FnMut`, `FnOnce`, a `fn` pointer, or a
/// parameter already in `callable`.
fn callable_type_params(
    generics: &[syn::Generics],
    mut callable: BTreeSet<String>,
) -> BTreeSet<String> {
    let mut bounded: Vec<(Vec<String>, TokenStream)> = Vec::new();
    for generics in generics {
        for param in generics.type_params() {
            bounded.push((vec![unraw(&param.ident)], param.bounds.to_token_stream()));
        }
        for predicate in generics
            .where_clause
            .iter()
            .flat_map(|clause| &clause.predicates)
        {
            if let syn::WherePredicate::Type(predicate) = predicate {
                let mut names = Vec::new();
                token_idents(&predicate.bounded_ty.to_token_stream(), &mut names);
                bounded.push((names, predicate.bounds.to_token_stream()));
            }
        }
    }
    loop {
        let before = callable.len();
        for (names, bounds) in &bounded {
            if tokens_name_callable(bounds, &callable) {
                callable.extend(names.iter().cloned());
            }
        }
        if callable.len() == before {
            return callable;
        }
    }
}

/// The names bound by the value parameters of `sig` whose type is callable:
/// it names `Fn`, `FnMut`, `FnOnce` or a `fn` pointer (`impl Fn()`, `&dyn
/// Fn()`, `Box<dyn FnMut()>`, `fn() -> u64`), or a generic parameter of `sig`
/// or of `outer_callable_types` that is callable.
fn callable_params(
    sig: &syn::Signature,
    outer_callable_types: &BTreeSet<String>,
) -> BTreeSet<String> {
    let callable = callable_type_params(
        std::slice::from_ref(&sig.generics),
        outer_callable_types.clone(),
    );
    let mut names = BTreeSet::new();
    for input in &sig.inputs {
        let syn::FnArg::Typed(typed) = input else {
            continue;
        };
        if tokens_name_callable(&typed.ty.to_token_stream(), &callable) {
            let mut binder = PatNames::default();
            binder.visit_pat(&typed.pat);
            names.extend(binder.names);
        }
    }
    names
}

/// A name of `params` that `mentions` counts twice, or once inside a loop or
/// a closure.
fn repeated_callable_param(params: &BTreeSet<String>, mentions: &[Mention]) -> Option<String> {
    params
        .iter()
        .find(|param| {
            let mut hits = mentions.iter().filter(|mention| &mention.name == *param);
            match (hits.next(), hits.next()) {
                (Some(_), Some(_)) => true,
                (Some(only), None) => only.repeated,
                _ => false,
            }
        })
        .cloned()
}

fn tokens_name_callable(tokens: &TokenStream, callable: &BTreeSet<String>) -> bool {
    tokens.clone().into_iter().any(|tree| match tree {
        TokenTree::Ident(ident) => {
            let name = unraw(&ident);
            CALLABLE_TYPE_IDENTS.contains(&name.as_str()) || callable.contains(&name)
        }
        TokenTree::Group(group) => tokens_name_callable(&group.stream(), callable),
        TokenTree::Punct(_) | TokenTree::Literal(_) => false,
    })
}

fn token_idents(tokens: &TokenStream, out: &mut Vec<String>) {
    for tree in tokens.clone() {
        match tree {
            TokenTree::Ident(ident) => out.push(unraw(&ident)),
            TokenTree::Group(group) => token_idents(&group.stream(), out),
            TokenTree::Punct(_) | TokenTree::Literal(_) => {}
        }
    }
}

/// The names a pattern binds.
#[derive(Default)]
struct PatNames {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for PatNames {
    fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
        self.names.push(unraw(&pat.ident));
        syn::visit::visit_pat_ident(self, pat);
    }
}

fn returns_a_value(output: &syn::ReturnType) -> bool {
    match output {
        syn::ReturnType::Default => false,
        syn::ReturnType::Type(_, ty) => type_is_a_value(ty),
    }
}

/// False for `()` and `!`, which have at most one value.
fn type_is_a_value(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Tuple(tuple) => !tuple.elems.is_empty(),
        syn::Type::Never(_) => false,
        syn::Type::Paren(paren) => type_is_a_value(&paren.elem),
        syn::Type::Group(group) => type_is_a_value(&group.elem),
        _ => true,
    }
}

/// What [`fn_mentions`] reads from a function.
struct FnScan {
    mentions: Vec<Mention>,
    /// The first comparison of values of a generic type in its executable
    /// code.
    comparison: Option<String>,
    /// The first comparison in its executable code of values of a type
    /// whose impl the file does not show, when it has none of the above.
    foreign_comparison: Option<String>,
    /// The first clause the `trust_vc` macros check at run time that
    /// compares values of a generic type or of a type whose impl the file
    /// does not show.
    checked_comparison: Option<String>,
    /// The same, in a precondition.
    checked_precondition: Option<String>,
}

/// What the check of the clauses the `trust_vc` macros evaluate at run time
/// reads from the file (see [`super::runtime_checked_clauses`]).
struct ClauseInputs {
    /// The type names whose comparison the lane may read otherwise than the
    /// check runs it.
    opaque: BTreeSet<String>,
    /// The `const`s and `static`s of those types.
    opaque_values: BTreeSet<String>,
    /// The file's declarations, with `opaque` read as generic.
    decls: FileDecls,
}

impl ClauseInputs {
    fn new(file: Option<&File>) -> Self {
        let opaque = opaque_type_names(file);
        let opaque_values = opaque_value_names(file, &opaque);
        let decls = FileDecls::with_opaque(file, &opaque);
        ClauseInputs {
            opaque,
            opaque_values,
            decls,
        }
    }
}

/// The reading of one function that takes the file's opaque type names as
/// generic, for its clauses the macros evaluate at run time and for the
/// comparisons in its executable code; its scope is built on first use.
struct ClauseContext<'s> {
    inputs: &'s ClauseInputs,
    outer: OuterContext,
    sig: &'s syn::Signature,
    block: Option<&'s syn::Block>,
    scope: OnceCell<Option<GenericScope<'s>>>,
}

impl<'s> ClauseContext<'s> {
    fn new(
        inputs: &'s ClauseInputs,
        outer: &OuterContext,
        sig: &'s syn::Signature,
        block: Option<&'s syn::Block>,
    ) -> Self {
        let mut type_params = outer.type_params.clone();
        type_params.extend(inputs.opaque.iter().cloned());
        ClauseContext {
            inputs,
            outer: OuterContext {
                type_params,
                self_kind: outer.opaque_self_kind,
                opaque_self_kind: None,
            },
            sig,
            block,
            scope: OnceCell::new(),
        }
    }

    fn scope(&self) -> Option<&GenericScope<'s>> {
        self.scope
            .get_or_init(|| {
                GenericScope::new(&self.inputs.decls, &self.outer, self.sig, self.block)
            })
            .as_ref()
    }

    /// True when `clause` compares values whose comparison the lane may read
    /// otherwise than the check runs it.
    fn opaque_comparison(&self, clause: &CheckedClause) -> bool {
        self.scope()
            .is_some_and(|scope| compares_opaque_values(scope, clause, &self.inputs.opaque_values))
    }
}

impl Reading for ClauseContext<'_> {
    /// Not concrete when `expr` may hold a value of an opaque type, or names
    /// a `const` or `static` of one.
    fn kind(&self, expr: &syn::Expr) -> Kind {
        if names_any(&expr.to_token_stream(), &self.inputs.opaque_values) {
            return Kind::Generic;
        }
        self.scope()
            .map_or(Kind::Concrete, |scope| scope.expr_kind(expr))
    }

    fn tokens_mention(&self, tokens: &TokenStream) -> bool {
        names_any(tokens, &self.inputs.opaque_values)
            || self
                .scope()
                .is_some_and(|scope| scope.tokens_mention(tokens))
    }
}

/// Which values a comparison may run an impl the lane does not read on.
trait Reading {
    /// How much of such a type the value of `expr` may carry.
    fn kind(&self, expr: &syn::Expr) -> Kind;
    /// True when `tokens` name such a type or a value that may carry one.
    fn tokens_mention(&self, tokens: &TokenStream) -> bool;
}

/// The reading of a function's generic values alone.
struct GenericReading<'a, 's>(Option<&'a GenericScope<'s>>);

impl Reading for GenericReading<'_, '_> {
    fn kind(&self, expr: &syn::Expr) -> Kind {
        self.0.map_or(Kind::Concrete, |scope| scope.expr_kind(expr))
    }

    fn tokens_mention(&self, tokens: &TokenStream) -> bool {
        self.0.is_some_and(|scope| scope.tokens_mention(tokens))
    }
}

/// The mentions in a function's attributes and body, and its comparisons of
/// values of a generic type. `scope` is `None` for a function with nothing
/// generic in reach, and `exec` is false for a spec or proof function.
fn fn_mentions<'s>(
    attrs: &[syn::Attribute],
    sig: &syn::Signature,
    block: Option<&syn::Block>,
    scope: Option<&'s GenericScope<'s>>,
    decls: &'s FileDecls,
    exec: bool,
    clause: ClauseContext<'s>,
) -> FnScan {
    let mut scan = MentionScan {
        depth: 0,
        spec_depth: usize::from(!exec),
        scope,
        decls,
        clause,
        returns_reference: matches!(
            &sig.output,
            syn::ReturnType::Type(_, ty) if returns_reference(ty)
        ),
        mentions: Vec::new(),
        comparison: None,
        foreign_comparison: None,
        checked_comparison: None,
        checked_precondition: None,
    };
    for attr in attrs {
        scan.visit_attribute(attr);
    }
    if let Some(block) = block {
        scan.visit_block(block);
    }
    FnScan {
        mentions: scan.mentions,
        comparison: scan.comparison,
        foreign_comparison: scan.foreign_comparison,
        checked_comparison: scan.checked_comparison,
        checked_precondition: scan.checked_precondition,
    }
}

fn returns_reference(ty: &syn::Type) -> bool {
    match ty {
        syn::Type::Reference(_) => true,
        syn::Type::Paren(paren) => returns_reference(&paren.elem),
        syn::Type::Group(group) => returns_reference(&group.elem),
        _ => false,
    }
}

/// Collects the names a body mentions, marking those inside a loop or a
/// closure. Items nested in the body are entries of their own and are not
/// read here.
struct MentionScan<'s> {
    depth: usize,
    /// Inside a contract, a proof macro, or a spec or proof function.
    spec_depth: usize,
    scope: Option<&'s GenericScope<'s>>,
    decls: &'s FileDecls,
    clause: ClauseContext<'s>,
    /// The function returns a reference.
    returns_reference: bool,
    mentions: Vec<Mention>,
    comparison: Option<String>,
    foreign_comparison: Option<String>,
    checked_comparison: Option<String>,
    checked_precondition: Option<String>,
}

impl MentionScan<'_> {
    /// Records `clause`, which the macros check at run time, when it is
    /// reached from running code and compares values whose comparison the
    /// lane may read otherwise than the check runs it.
    fn check_clause(&mut self, clause: &CheckedClause) {
        if self.spec_depth != 0 {
            return;
        }
        if !self.clause.opaque_comparison(clause) {
            return;
        }
        let site = format!("`{}`", clause.source);
        if clause.precondition && self.checked_precondition.is_none() {
            self.checked_precondition = Some(site.clone());
        }
        if self.checked_comparison.is_none() {
            self.checked_comparison = Some(site);
        }
    }

    fn mention(&mut self, ident: &syn::Ident) {
        self.mentions.push(Mention {
            name: unraw(ident),
            repeated: self.depth > 0,
        });
    }

    fn mention_path(&mut self, path: &syn::Path) {
        if let Some(segment) = path.segments.last() {
            self.mention(&segment.ident);
        }
    }

    /// Records an evaluation of `method` on a value of a generic type, unless
    /// the file declares `method` only as a spec function. `receiver_type`
    /// names the generic type of a receiver that is a parameter.
    fn mention_generic(&mut self, method: &str, receiver_type: Option<String>, repeated: bool) {
        if self.decls.is_spec_only(method) {
            return;
        }
        let name = match receiver_type {
            Some(ty) => format!("{GENERIC_METHOD_PREFIX}{method}{RECEIVER_TYPE_SEPARATOR}{ty}"),
            None => format!("{GENERIC_METHOD_PREFIX}{method}"),
        };
        self.mentions.push(Mention {
            name,
            repeated: repeated || self.depth > 0,
        });
    }

    fn repeating<F: FnOnce(&mut Self)>(&mut self, visit: F) {
        self.depth += 1;
        visit(self);
        self.depth -= 1;
    }

    fn spec<F: FnOnce(&mut Self)>(&mut self, visit: F) {
        self.spec_depth += 1;
        visit(self);
        self.spec_depth -= 1;
    }

    fn kind(&self, expr: &syn::Expr) -> Kind {
        self.scope
            .map_or(Kind::Concrete, |scope| scope.expr_kind(expr))
    }

    /// Records the comparison at `site` in executable code when `compares`
    /// finds that it compares values of a generic type, else when it finds
    /// that it compares values of a type whose impl the file does not show
    /// under the reading that takes the file's opaque type names as generic.
    fn compare<F>(&mut self, site: impl FnOnce() -> String, compares: F)
    where
        F: Fn(&dyn Reading) -> bool,
    {
        if self.spec_depth != 0 || self.comparison.is_some() {
            return;
        }
        if compares(&GenericReading(self.scope)) {
            self.comparison = Some(site());
        } else if self.foreign_comparison.is_none() && compares(&self.clause) {
            self.foreign_comparison = Some(site());
        }
    }

    /// Reads the tokens of a macro invocation or an attribute: as
    /// comma-separated expressions, else as statements, else token by token.
    /// Token by token, every identifier is a mention, and all of them count
    /// as repeated when the tokens hold a loop keyword or a `|`.
    fn tokens(&mut self, tokens: &TokenStream) {
        if let Ok(exprs) = syn::parse::Parser::parse2(
            Punctuated::<syn::Expr, Token![,]>::parse_terminated,
            tokens.clone(),
        ) {
            for expr in &exprs {
                self.visit_expr(expr);
            }
            return;
        }
        if let Ok(stmts) = syn::parse::Parser::parse2(syn::Block::parse_within, tokens.clone()) {
            for stmt in &stmts {
                self.visit_stmt(stmt);
            }
            return;
        }
        let repeats = tokens_may_repeat(tokens);
        if repeats {
            self.depth += 1;
        }
        self.raw_tokens(tokens);
        if repeats {
            self.depth -= 1;
        }
    }

    /// Token by token, where a generic value is in reach, an identifier
    /// written like a method call (`.m(`) on a generic name or on the result
    /// of a call or an index counts as a call of `m` on a generic value, and
    /// a comparison operator in executable code counts as a comparison of
    /// generic values; where only a value of an opaque type is in reach, it
    /// counts as a comparison of such values.
    fn raw_tokens(&mut self, tokens: &TokenStream) {
        let generic = self.scope.is_some_and(|scope| scope.tokens_mention(tokens));
        let trees: Vec<TokenTree> = tokens.clone().into_iter().collect();
        for (index, tree) in trees.iter().enumerate() {
            match tree {
                TokenTree::Ident(ident) => {
                    self.mention(ident);
                    let after_dot = index > 1
                        && matches!(&trees[index - 1], TokenTree::Punct(p) if p.as_char() == '.');
                    let before_call = matches!(
                        trees.get(index + 1),
                        Some(TokenTree::Group(group))
                            if group.delimiter() == proc_macro2::Delimiter::Parenthesis
                    );
                    let generic_receiver = after_dot
                        && match &trees[index - 2] {
                            TokenTree::Ident(receiver) => self.scope.is_some_and(|scope| {
                                scope.name_kind(&unraw(receiver)) == Kind::Generic
                            }),
                            TokenTree::Group(_) => true,
                            TokenTree::Punct(_) | TokenTree::Literal(_) => false,
                        };
                    if generic && generic_receiver && before_call {
                        self.mention_generic(&unraw(ident), None, false);
                    }
                }
                TokenTree::Group(group) => self.raw_tokens(&group.stream()),
                TokenTree::Punct(punct) => {
                    let comparison = matches!(punct.as_char(), '<' | '>')
                        || (matches!(punct.as_char(), '=' | '!')
                            && matches!(
                                trees.get(index + 1),
                                Some(TokenTree::Punct(next)) if next.as_char() == '='
                            ));
                    if comparison {
                        self.compare(
                            || "a comparison in the tokens of a macro".to_string(),
                            |reading| reading.tokens_mention(tokens),
                        );
                    }
                }
                TokenTree::Literal(_) => {}
            }
        }
    }
}

/// True when `reading` finds that comparing `left` with `right` compares
/// values whose impl the lane does not read: either may carry one, and
/// neither is a literal, whose type is a primitive.
fn compares_operands(reading: &dyn Reading, left: &syn::Expr, right: &syn::Expr) -> bool {
    !is_literal(left)
        && !is_literal(right)
        && reading.kind(left).max(reading.kind(right)) != Kind::Concrete
}

pub(super) fn is_literal(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Lit(_) => true,
        syn::Expr::Paren(inner) => is_literal(&inner.expr),
        syn::Expr::Group(inner) => is_literal(&inner.expr),
        syn::Expr::Reference(inner) => is_literal(&inner.expr),
        syn::Expr::Unary(inner) => is_literal(&inner.expr),
        _ => false,
    }
}

/// True when `path` names a macro that holds spec or proof code.
pub(super) fn is_spec_macro(path: &syn::Path) -> bool {
    let first = path.segments.first().map(|segment| unraw(&segment.ident));
    let last = path.segments.last().map(|segment| unraw(&segment.ident));
    (path.segments.len() > 1
        && first.is_some_and(|first| SPEC_MACRO_ROOTS.contains(&first.as_str())))
        || last.is_some_and(|last| SPEC_MACROS.contains(&last.as_str()))
}

fn tokens_may_repeat(tokens: &TokenStream) -> bool {
    tokens.clone().into_iter().any(|tree| match tree {
        TokenTree::Ident(ident) => ident == "while" || ident == "loop" || ident == "for",
        TokenTree::Punct(punct) => punct.as_char() == '|',
        TokenTree::Group(group) => tokens_may_repeat(&group.stream()),
        TokenTree::Literal(_) => false,
    })
}

impl<'ast> Visit<'ast> for MentionScan<'_> {
    fn visit_item(&mut self, _item: &'ast syn::Item) {}

    fn visit_expr_while(&mut self, expr: &'ast syn::ExprWhile) {
        self.repeating(|scan| syn::visit::visit_expr_while(scan, expr));
    }

    fn visit_expr_loop(&mut self, expr: &'ast syn::ExprLoop) {
        self.repeating(|scan| syn::visit::visit_expr_loop(scan, expr));
    }

    fn visit_expr_for_loop(&mut self, expr: &'ast syn::ExprForLoop) {
        self.repeating(|scan| syn::visit::visit_expr_for_loop(scan, expr));
    }

    fn visit_expr_closure(&mut self, expr: &'ast syn::ExprClosure) {
        self.repeating(|scan| syn::visit::visit_expr_closure(scan, expr));
    }

    fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
        self.mention_path(&expr.path);
        // A method of a generic type named as a value (`let g = T::make;`)
        // can be called any number of times.
        if let Some(method) = self
            .scope
            .and_then(|scope| scope.generic_path_method(expr, None))
        {
            self.mention_generic(&method, None, true);
        }
        syn::visit::visit_expr_path(self, expr);
    }

    fn visit_expr_call(&mut self, expr: &'ast syn::ExprCall) {
        let syn::Expr::Path(path) = &*expr.func else {
            syn::visit::visit_expr_call(self, expr);
            return;
        };
        self.mention_path(&path.path);
        if let Some(method) = self
            .scope
            .and_then(|scope| scope.generic_path_method(path, expr.args.first()))
        {
            self.mention_generic(&method, None, false);
        }
        // `PartialEq::eq(&x, &y)`, `T::cmp(&x, &y)`, `std::cmp::max(x, y)`.
        let comparison_method = path
            .path
            .segments
            .last()
            .is_some_and(|last| COMPARISON_METHODS.contains(&unraw(&last.ident).as_str()));
        if comparison_method {
            self.compare(
                || format!("`{}`", path.to_token_stream()),
                |reading| {
                    expr.args
                        .iter()
                        .any(|arg| reading.kind(arg) != Kind::Concrete)
                },
            );
        }
        for arg in &expr.args {
            self.visit_expr(arg);
        }
    }

    fn visit_expr_binary(&mut self, expr: &'ast syn::ExprBinary) {
        if is_comparison(&expr.op) {
            self.compare(
                || format!("`{}`", expr.op.to_token_stream()),
                |reading| compares_operands(reading, &expr.left, &expr.right),
            );
        }
        syn::visit::visit_expr_binary(self, expr);
    }

    fn visit_expr_method_call(&mut self, expr: &'ast syn::ExprMethodCall) {
        self.mention(&expr.method);
        // `f.requires(args)` and `f.ensures(args, r)` state the contract of
        // the closure `f` without calling it, so `f` is not a mention there.
        let reflection = (expr.method == "requires" || expr.method == "ensures")
            && matches!(
                &*expr.receiver,
                syn::Expr::Path(path) if path.qself.is_none() && path.path.get_ident().is_some()
            );
        if reflection {
            for arg in &expr.args {
                self.visit_expr(arg);
            }
            return;
        }
        let method = unraw(&expr.method);
        let receiver = self.kind(&expr.receiver);
        if receiver == Kind::Generic {
            let receiver_type = self
                .scope
                .and_then(|scope| scope.receiver_type(&expr.receiver));
            self.mention_generic(&method, receiver_type, false);
        }
        let comparison_method = COMPARISON_METHODS.contains(&method.as_str());
        let element_comparison_method = ELEMENT_COMPARISON_METHODS.contains(&method.as_str());
        if comparison_method || element_comparison_method {
            self.compare(
                || format!("`.{method}(..)`"),
                |reading| {
                    let receiver = reading.kind(&expr.receiver);
                    let args = expr
                        .args
                        .iter()
                        .map(|arg| reading.kind(arg))
                        .max()
                        .unwrap_or(Kind::Concrete);
                    (comparison_method && receiver.max(args) != Kind::Concrete)
                        || (element_comparison_method
                            && receiver != Kind::Concrete
                            && args != Kind::Concrete)
                },
            );
        }
        syn::visit::visit_expr_method_call(self, expr);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        let name = mac
            .path
            .segments
            .last()
            .map(|segment| unraw(&segment.ident))
            .unwrap_or_default();
        if is_spec_macro(&mac.path) {
            if let Some(clause) = checked_macro_clause(mac) {
                self.check_clause(&clause);
            }
            self.spec(|scan| scan.tokens(&mac.tokens));
            return;
        }
        if COMPARISON_MACROS.contains(&name.as_str()) {
            if let Ok(args) = syn::parse::Parser::parse2(
                Punctuated::<syn::Expr, Token![,]>::parse_terminated,
                mac.tokens.clone(),
            ) {
                let mut args = args.iter();
                if let (Some(left), Some(right)) = (args.next(), args.next()) {
                    self.compare(
                        || format!("`{name}!`"),
                        |reading| compares_operands(reading, left, right),
                    );
                }
            } else {
                self.compare(
                    || format!("`{name}!`"),
                    |reading| reading.tokens_mention(&mac.tokens),
                );
            }
        }
        self.tokens(&mac.tokens);
    }

    fn visit_attribute(&mut self, attr: &'ast syn::Attribute) {
        for clause in checked_attribute_clauses(attr, self.returns_reference) {
            self.check_clause(&clause);
        }
        self.spec(|scan| match &attr.meta {
            syn::Meta::Path(_) => {}
            syn::Meta::List(list) => scan.tokens(&list.tokens),
            syn::Meta::NameValue(name_value) => scan.visit_expr(&name_value.value),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn refusal(src: &str) -> Option<String> {
        let file = syn::parse_file(src).expect("fixture parses");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == "f" => Some(func.clone()),
                _ => None,
            })
            .expect("fixture has `fn f`");
        verified_refusal(Some(&file), &func)
    }

    const ROOT: &str = "#[trust_vc::external_body] #[trust_vc::ensures(result < 100u64)] \
                        fn r() -> u64 { 0 }";

    #[test]
    fn repeated_evaluation_of_a_bodiless_function_is_refused() {
        for body in [
            "fn f() { let a = r(); let b = r(); }",
            "fn f() -> u64 { r() - r() }",
            "fn f() { trust_vc::assert!(r() == r()); }",
            "fn f() { let a = r(); trust_vc::assert!(a == r()); }",
            "fn f() { while true { let a = r(); } }",
            "fn f() { loop { r(); } }",
            "fn f() { for i in 0..3 { r(); } }",
            "fn f() { let c = || r(); }",
            "fn f() { let a = wrap(); let b = r(); } fn wrap() -> u64 { r() }",
            "fn f() { let a = wrap(); let b = wrap(); } fn wrap() -> u64 { r() }",
            "fn f() { let a = w2(); let b = r(); } fn w2() -> u64 { wrap() } fn wrap() -> u64 { r() }",
            "fn f() { let a = g(); } fn g() -> u64 { while true { r(); } 0 }",
            "#[trust_vc::ensures(result == r())] fn f() -> u64 { r() }",
            "fn f() { let a = h(); let b = r(); } #[trust_vc::ensures(result == r())] fn h() -> u64 { 0 }",
            "fn f(n: u64) -> u64 { if n == 0 { 0 } else { r() + f(n - 1) } }",
            "fn f() { let a = rec(3); } fn rec(n: u64) -> u64 { if n == 0 { r() } else { rec(n - 1) } }",
            "use self::r as q; fn f() { let a = q(); let b = q(); }",
            "fn f() { let a = r(); let b = crate::r(); }",
            "fn f() { let a = r(); let b = S::r(); }",
            "fn f() { trust_vc::proof! { r(); r(); } }",
            "fn f() { m!(r, r, |x| x); }",
        ] {
            let src = format!("{ROOT} {body}");
            assert!(refusal(&src).is_some(), "not refused: {src}");
        }
    }

    #[test]
    fn repeated_evaluation_of_a_bodiless_method_is_refused() {
        for src in [
            "struct S; impl S { #[trust_vc::external_body] fn get(&self) -> u64 { 0 } } \
             fn f(s: S) { let a = s.get(); let b = s.get(); }",
            "struct S; #[trust_vc::external_body] impl S { fn get(&self) -> u64 { 0 } } \
             fn f(s: S) { let a = s.get(); let b = S::get(&s); }",
            "#[trust_vc::external] mod m { pub fn get() -> u64 { 0 } } \
             fn f() { let a = m::get(); let b = m::get(); }",
            "#[verifier::external_body] fn get() -> bool { true } \
             fn f() { let a = get(); let b = get(); }",
            "struct S; impl S { #[trust_vc::external_body] fn get(&self) -> u64 { 0 } } \
             trait T { fn m(&self) -> u64; } impl T for S { fn m(&self) -> u64 { self.get() } } \
             fn f(s: S) { let a = s.m(); let b = s.m(); }",
        ] {
            assert!(refusal(src).is_some(), "not refused: {src}");
        }
    }

    #[test]
    fn a_bodiless_method_an_operator_invokes_refuses_the_file() {
        let src = "struct S(u64); \
                   impl PartialEq for S { #[trust_vc::external_body] fn eq(&self, o: &S) -> bool { true } } \
                   fn f() {}";
        assert!(refusal(src).is_some());
        let src = "struct S(u64); \
                   impl core::ops::Add for S { type Output = S; fn add(self, o: S) -> S { S(r()) } } \
                   fn f() {}";
        assert!(refusal(&format!("{ROOT} {src}")).is_some());
    }

    #[test]
    fn one_evaluation_of_each_bodiless_function_is_not_refused() {
        for body in [
            "fn f() { let a = r(); }",
            "fn f() -> u64 { r() + 1u64 }",
            "fn f() { let a = r(); let b = s(); } \
             #[trust_vc::external_body] fn s() -> u64 { 0 }",
            "fn f() { let a = wrap(); } fn wrap() -> u64 { r() }",
            "fn f() { let a = r(); let b = g(); let c = g(); } fn g() -> u64 { 5 }",
            "fn f() { let a = r(); let b = fib(3); } fn fib(n: u64) -> u64 { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }",
            "fn f() { let a = r(); while true { let b = g(); } } fn g() -> u64 { 5 }",
            "fn f() { let a = r(); unit(); unit(); } #[trust_vc::external_body] fn unit() {}",
            "fn f() { let a = r(); c(); c(); } #[trust_vc::external_body] const fn c() -> u64 { 1 }",
            "fn f() { let a = r(); sp(); sp(); } #[trust_vc::spec] #[trust_vc::external_body] fn sp() -> u64 { 1 }",
            "fn f() { let a = r(); } fn other() { let a = r(); let b = r(); }",
            "fn f() { let a = r(); fn inner() { r(); r(); } }",
        ] {
            let src = format!("{ROOT} {body}");
            assert_eq!(refusal(&src), None, "refused: {src}");
        }
        assert_eq!(
            refusal("fn g() -> u64 { 1 } fn f() { let a = g(); let b = g(); }"),
            None
        );
    }

    fn method_refusal(src: &str) -> Option<String> {
        let file = syn::parse_file(src).expect("fixture parses");
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Impl(item) => item.items.iter().find_map(|item| match item {
                    syn::ImplItem::Fn(method) if method.sig.ident == "f" => Some(ItemFn {
                        attrs: method.attrs.clone(),
                        vis: method.vis.clone(),
                        sig: method.sig.clone(),
                        block: Box::new(method.block.clone()),
                    }),
                    _ => None,
                }),
                _ => None,
            })
            .expect("fixture has method `f`");
        verified_refusal(Some(&file), &func)
    }

    #[test]
    fn a_callable_parameter_evaluated_twice_is_refused() {
        for src in [
            "fn f<F: Fn() -> u64>(g: F) { let a = g(); let b = g(); }",
            "fn f<F>(g: F) where F: Fn() -> u64 { g(); g(); }",
            "fn f(g: impl Fn() -> u64) { g(); g(); }",
            "fn f(g: &dyn Fn() -> u64) { g(); g(); }",
            "fn f(mut g: Box<dyn FnMut() -> u64>) { g(); g(); }",
            "fn f(g: fn() -> u64) { g(); g(); }",
            "fn f<F: Fn() -> u64>(g: &F) { g(); g(); }",
            "fn f<F: Fn() -> u64, G: AsRef<F>>(g: G) { g.as_ref()(); g.as_ref()(); }",
            "fn f<F: Fn() -> u64>((g, h): (F, F)) { g(); g(); }",
            "fn f<F: Fn(u64) -> u64>(g: F, x: u64, y: u64) { trust_vc::assert!(g(x) == g(y)); }",
            "fn f<F: Fn() -> u64>(g: F) { while true { g(); } }",
            "fn f<F: Fn() -> u64>(g: F) { for i in 0..3 { g(); } }",
            "fn f<F: Fn() -> u64>(g: F) { let c = || g(); }",
            "#[trust_vc::ensures(result == g())] fn f<F: Fn() -> u64>(g: F) -> u64 { g() }",
            "fn f<F: Fn() -> u64>(g: F) { let a = h(&g); let b = g(); } \
             fn h<G: Fn() -> u64>(k: &G) -> u64 { k() }",
            "fn f<F: Fn() -> u64>(g: F) { trust_vc::proof! { g(); g(); } }",
        ] {
            let message = refusal(src).unwrap_or_else(|| panic!("not refused: {src}"));
            assert!(message.contains("callable type"), "{message}");
        }
        let src = "struct S<F>(F); impl<F: Fn() -> u64> S<F> { fn f(g: F) { g(); g(); } }";
        assert!(method_refusal(src).is_some(), "not refused: {src}");
    }

    #[test]
    fn a_function_that_repeats_a_callable_parameter_refuses_what_reaches_it() {
        for src in [
            "fn twice<G: Fn() -> u64>(g: G) -> bool { g() == g() } \
             fn f<F: Fn() -> u64>(k: F) -> bool { twice(k) }",
            "fn twice<G: Fn() -> u64>(g: G) -> bool { g() == g() } \
             fn mid<G: Fn() -> u64>(g: G) -> bool { twice(g) } \
             fn f<F: Fn() -> u64>(k: F) -> bool { mid(k) }",
            "fn spin<G: Fn() -> u64>(g: G) { loop { g(); } } fn f() { spin(|| 1u64); }",
        ] {
            let message = refusal(src).unwrap_or_else(|| panic!("not refused: {src}"));
            assert!(message.contains("callable parameters"), "{message}");
        }
    }

    #[test]
    fn one_evaluation_of_each_callable_parameter_is_not_refused() {
        for src in [
            "fn f<F: Fn() -> u64>(g: F) -> u64 { g() }",
            "fn f<F: Fn() -> u64, G: Fn() -> u64>(g: F, h: G) -> u64 { g() + h() }",
            "#[trust_vc::requires(g.requires((a,)))] #[trust_vc::ensures(g.ensures((a,), result))] \
             fn f<F: Fn(u64) -> u64>(g: F, a: u64) -> u64 { g(a) }",
            "fn f<F: Fn() -> u64>(g: F) -> u64 { h(&g) } fn h<G: Fn() -> u64>(k: &G) -> u64 { k() }",
            "fn f<T: Clone>(x: T) { let a = x.clone(); }",
            "fn f(x: u64, s: SpecFn<u64, u64>) { let a = x; let b = x; let c = s(1); let d = s(1); }",
            "fn f<F: Fn() -> u64>(g: F) -> u64 { fn inner<G: Fn() -> u64>(k: G) { k(); k(); } g() }",
            "fn f() -> u64 { 1 } fn other<G: Fn() -> u64>(g: G) -> bool { g() == g() }",
        ] {
            assert_eq!(refusal(src), None, "refused: {src}");
        }
    }

    const TR: &str = "trait Tr { fn read(&self) -> u64; } trait Mk { fn make() -> u64; }";

    #[test]
    fn a_method_of_a_generic_value_evaluated_twice_is_refused() {
        for body in [
            "fn f<T: Tr>(t: &T) { let a = t.read(); let b = t.read(); }",
            "fn f<T: Tr>(t: T) -> u64 { t.read() - t.read() }",
            "fn f<T>(t: &T) where T: Tr { t.read(); t.read(); }",
            "fn f(t: impl Tr) { t.read(); t.read(); }",
            "fn f(t: &dyn Tr) { t.read(); t.read(); }",
            "fn f(t: Box<dyn Tr>) { t.read(); t.read(); }",
            "fn f<T: Tr>(p: (T, T)) { p.0.read(); p.1.read(); }",
            "fn f<T: Tr>(v: &Vec<T>) { v[0].read(); v[1].read(); }",
            "fn f<T: Tr>(t: T) { let u = t; u.read(); u.read(); }",
            "fn f<T: Tr>(x: T, y: T) { let p = (x, y); p.0.read(); p.1.read(); }",
            "fn f<T: Tr>(t: &T) { while true { t.read(); } }",
            "fn f<T: Tr>(t: &T) { let c = || t.read(); }",
            "fn f<T: Tr>(v: &Vec<T>) { for x in v.iter() { x.read(); } }",
            "fn f<T: Mk>() { T::make(); T::make(); }",
            "fn f<T: Mk>() { <T as Mk>::make(); <T as Mk>::make(); }",
            "fn f<T: Tr>(t: &T) { Tr::read(t); Tr::read(t); }",
            "fn f<T: Mk>() { let g = T::make; }",
            "#[trust_vc::requires(t.read() == 5u64)] fn f<T: Tr>(t: &T) { t.read(); }",
            "#[trust_vc::ensures(result == t.read())] fn f<T: Tr>(t: &T) -> u64 { t.read() }",
            "fn w<T: Tr>(t: &T) -> u64 { t.read() } fn f<T: Tr>(t: &T) { w(t); w(t); }",
            "fn f<T: Tr>(t: &T, n: u64) -> u64 { if n == 0u64 { 0u64 } else { t.read() + f(t, n - 1u64) } }",
            "fn f<T: Tr>(t: &T) { m!(t.read(), t.read()); }",
            "fn f<T: Tr>(x: &T, y: &T) -> u64 { x.read() + y.read() }",
            "fn f<T: Tr, U: Tr>(x: &T, y: &U) { let x = y; x.read(); y.read(); }",
            "fn f<T: Tr, U: Tr>(x: &T, y: &U) -> u64 { x.read() + w(y) } \
             fn w<V: Tr>(v: &V) -> u64 { v.read() }",
            "fn f<T: Tr>(o: Option<T>) { o.unwrap().read(); o.unwrap().read(); }",
            "fn f<T: Tr>(o: Option<T>, t: T) -> u64 { o.map_or(t, |x| x).read() + o.unwrap().read() }",
            "fn f<T: Tr>(v: &Vec<T>) { v.get(0).unwrap().read(); v.get(1).unwrap().read(); } \
             struct S; impl S { fn get(&self, i: usize) -> u64 { 1 } }",
        ] {
            let src = format!("{TR} {body}");
            let message = refusal(&src).unwrap_or_else(|| panic!("not refused: {src}"));
            assert!(message.starts_with(BODILESS_CALL_REPEAT_TAG), "{message}");
        }
        let src = format!(
            "{TR} struct H<T>(T); impl<T: Tr> H<T> {{ fn f(&self) {{ self.0.read(); self.0.read(); }} }}"
        );
        assert!(method_refusal(&src).is_some(), "not refused: {src}");
        let src = format!("{TR} struct S; impl Tr for S {{ fn read(&self) -> u64 {{ 1 }} }} \
             trait U {{ fn f(&self) -> u64; }} impl<T: Tr> U for T {{ fn f(&self) -> u64 {{ self.read() + self.read() }} }}");
        assert!(method_refusal(&src).is_some(), "not refused: {src}");
    }

    #[test]
    fn one_evaluation_of_each_generic_method_is_not_refused() {
        for body in [
            "fn f<T: Tr>(t: &T) -> u64 { t.read() }",
            "fn f<T: Tr>(t: &T) { let a = t.read(); assert!(a == a); }",
            "fn f<T: Tr>(t: &T, n: u64) -> u64 { let a = t.read(); a + n }",
            "fn f<T: Tr>(v: &Vec<T>) -> usize { v.len() + v.len() }",
            "fn f<T: Tr>(t: &T, s: &S) { s.get(); s.get(); t.read(); } \
             struct S; impl S { fn get(&self) -> u64 { 1 } }",
            "fn f(s: &S) { s.read(); s.read(); } struct S; impl Tr for S { fn read(&self) -> u64 { 1 } }",
            "fn f<T: Tr>(t: &T) { let a = t.read(); fn inner<U: Tr>(u: &U) { u.read(); u.read(); } }",
            "fn f<T: Tr, U: Tr>(x: &T, y: &U) -> u64 { x.read() + y.read() }",
            "fn f(x: impl Tr, y: impl Tr) -> u64 { x.read() + y.read() }",
            "fn f<V>(a: V, b: V) { \
             trust_vc::assert!(Multiset::<V>::empty().insert(a).insert(b).count(a) == 1usize); }",
            "fn f<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>) { \
             trust_vc::assert!(a.add(b).add(c) == a.add(b.add(c))); }",
        ] {
            let src = format!("{TR} {body}");
            assert_eq!(refusal(&src), None, "refused: {src}");
        }
        let src = "trait V { #[trust_vc::spec] fn view(&self) -> u64; } \
                   #[trust_vc::requires(t.view() > 0u64)] \
                   fn f<T: V>(t: &T) { trust_vc::assert!(t.view() > 0u64); }";
        assert_eq!(refusal(src), None, "refused: {src}");
    }

    #[test]
    fn a_comparison_of_generic_values_in_executable_code_is_refused() {
        for src in [
            "fn f<T: PartialEq>(x: T) { assert!(x == x); }",
            "fn f<T: PartialEq>(x: T, y: T) -> bool { x != y }",
            "fn f<T: PartialOrd>(x: T, y: T) -> bool { x < y }",
            "fn f<T: PartialEq + std::fmt::Debug>(x: T) { assert_eq!(x, x); }",
            "fn f<T: PartialEq>(v: Vec<T>) -> bool { v == v }",
            "fn f<T: PartialEq>(p: (T, T)) -> bool { p.0 == p.1 }",
            "fn f<T: PartialEq>(x: T, y: T) -> bool { let p = (x, y); p.0 == p.1 }",
            "fn f<T: PartialEq>(x: &T, y: &T) -> bool { *x == *y }",
            "fn f<T: PartialEq + Copy>(x: T) -> bool { Some(x) == Some(x) }",
            "fn f(x: impl PartialEq + Copy) -> bool { x == x }",
            "fn f<T: PartialEq>(x: T) -> bool { x.eq(&x) }",
            "fn f<T: PartialEq>(x: T) -> bool { PartialEq::eq(&x, &x) }",
            "fn f<T: Ord>(x: T, y: T) -> T { x.max(y) }",
            "fn f<T: Ord>(x: T, y: T) -> T { std::cmp::max(x, y) }",
            "fn f<T: PartialEq>(v: &Vec<T>, x: &T) -> bool { v.contains(x) }",
            "fn f<T: PartialEq>(v: &Vec<T>) -> bool { v.iter().any(|y| *y == v[0]) }",
            "fn f<T: PartialEq>(x: T, y: T) { if x == y { assert!(y == x); } }",
            "#[trust_vc::requires(x == y)] fn f<T: PartialEq>(x: T, y: T) { assert!(x == y); }",
            "fn same<T: PartialEq>(a: &T, b: &T) -> bool { a == b } fn f(x: u64) -> bool { same(&x, &x) }",
            "struct W<T>(T); impl<T: PartialEq> PartialEq for W<T> { fn eq(&self, o: &Self) -> bool { self.0 == o.0 } } \
             fn f() {}",
        ] {
            let message = refusal(src).unwrap_or_else(|| panic!("not refused: {src}"));
            assert!(message.starts_with(GENERIC_COMPARISON_TAG), "{message}");
        }
        let src =
            "struct H<W>(W); impl<W: PartialEq> H<W> { fn f(&self) -> bool { self.0 == self.0 } }";
        assert!(method_refusal(src).is_some(), "not refused: {src}");
    }

    #[test]
    fn a_comparison_in_spec_code_or_of_concrete_values_is_not_refused() {
        for src in [
            "#[trust_vc::requires(x == y)] #[trust_vc::ensures(result == x)] \
             fn f<T: PartialEq>(x: T, y: T) -> T { y }",
            "fn f<T: PartialEq>(x: T) { trust_vc::proof! { assert(x == x); } }",
            "fn f<T: PartialEq>(x: T) { trust_vc::assert!(g(x) == g(x)); }",
            "#[trust_vc::spec] fn f<T: PartialEq>(x: T) -> bool { x == x }",
            "#[trust_vc::proof] fn f<T: PartialEq>(x: T) { assert!(x == x); }",
            "fn f<T>(v: &Vec<T>, i: usize) -> bool { i == 0usize && v.len() == i }",
            "fn f<T: PartialEq>(x: T, n: u64, m: u64) -> bool { n == m }",
            "trait Tr { fn read(&self) -> u64; } fn f<T: Tr>(t: &T) -> bool { t.read() == 5u64 }",
            "fn f(x: u64, y: u64) -> bool { x == y }",
        ] {
            assert_eq!(refusal(src), None, "refused: {src}");
        }
    }

    #[test]
    fn a_comparison_the_macros_check_at_run_time_is_refused() {
        for src in [
            "fn f<T: PartialEq>(x: T) { trust_vc::assert!(x == x); }",
            "#[trust_vc::contract(ensures(r == x), returns(r))] fn f<T: PartialEq>(x: T) -> T { x }",
            "use other::S; #[trust_vc::contract(ensures(r == s), returns(r))] fn f(s: S) -> S { s }",
            "#[trust_vc::contract(requires(a == b), ensures(true), returns(r))] \
             fn g<T: PartialEq>(a: T, b: T) {} fn f(x: u64) { g(x, x); }",
            "struct P(u64); impl core::ops::Add for P { type Output = P; fn add(self, o: P) -> P { g(1u64, 1u64); o } } \
             #[trust_vc::contract(requires(a == b), ensures(true), returns(r))] \
             fn g<T: PartialEq>(a: T, b: T) {} fn f() {}",
        ] {
            let message = refusal(src).unwrap_or_else(|| panic!("not refused: {src}"));
            assert!(message.starts_with(CHECKED_COMPARISON_TAG), "{src}: {message}");
        }
        for src in [
            "#[trust_vc::contract(ensures(r == x), returns(r))] fn f(x: u64) -> u64 { x }",
            "#[trust_vc::contract(ensures(r == inc(x)), returns(r))] fn f<T: PartialEq>(x: T) -> T { x }",
            "#[trust_vc::contract(ensures(r == 0u64), returns(r))] fn f<T: PartialEq>(x: T) -> u64 { 0u64 }",
            "#[derive(PartialEq)] struct Q { a: u64 } \
             #[trust_vc::contract(ensures(r == q), returns(r))] fn f(q: Q) -> Q { q }",
            "#[trust_vc::spec] fn f<T: PartialEq>(x: T) -> bool { trust_vc::assert!(x == x); true }",
            "fn f<T: PartialEq>(x: T) { proof_block! { trust_vc::assert!(x == x); } }",
        ] {
            assert_eq!(refusal(src), None, "refused: {src}");
        }
    }

    #[test]
    fn a_comparison_in_running_code_of_a_type_another_file_declares_is_refused() {
        for src in [
            "use other::S; fn f(s: S) { assert!(s == s); }",
            "mod other; use other::S; fn f(s: S) -> bool { s == s }",
            "use dep::S; fn f(s: S, t: S) { if s < t {} }",
            "use dep::S; fn f(s: S) { assert_eq!(s, s); }",
            "use dep::S; fn f(s: S) { assert!(s.eq(&s)); }",
            "use dep::S; fn f(s: S) { assert!(PartialEq::eq(&s, &s)); }",
            "use dep::S; fn f(s: S) { let v = vec![s]; assert!(v.contains(&s)); }",
            "use dep::S; fn f(s: S) { let p = (s, 1u64); assert!(p == p); }",
            "use dep::S; fn f(v: Vec<S>) { assert!(v == v); }",
            "use dep::S; fn f(s: S) { let t = s; assert!(t == s); }",
            "use dep::S; fn f(s: S) { println!(\"{}\", s == s); }",
            "use dep::S; #[derive(PartialEq)] struct W { s: S } fn f(w: W) { assert!(w == w); }",
            "use dep::S; fn same(s: &S) -> bool { s == s } fn f(s: S) { assert!(same(&s)); }",
            "use dep::S; const C: S = S::new(); fn f() { assert!(C == C); }",
            "mod other; struct T { a: u64 } fn f(t: T) { assert!(t == t); }",
            "fn f(s: dep::S) { assert!(s == s); }",
            "use dep::S; struct P(u64); impl core::ops::Add for P { type Output = P; \
             fn add(self, o: P) -> P { let s: S = S::new(); if s == s {} o } } fn f() {}",
        ] {
            let message = refusal(src).unwrap_or_else(|| panic!("not refused: {src}"));
            assert!(
                message.starts_with(FOREIGN_COMPARISON_TAG),
                "{src}: {message}"
            );
        }
    }

    #[test]
    fn a_comparison_whose_impl_the_file_shows_or_derives_is_not_refused() {
        for src in [
            "use dep::S; fn f(s: S, n: u64) { assert!(n == 1u64); }",
            "use dep::S; fn f(s: S, n: u64, m: u64) { assert!(n == m); }",
            "use dep::S; fn f(s: String) { assert!(s == s); }",
            "use std::collections::BTreeSet; fn f(s: BTreeSet<u64>) { assert!(s == s); }",
            "#[derive(PartialEq)] struct Q { a: u64 } fn f(q: Q) { assert!(q == q); }",
            "struct T { a: u64 } impl PartialEq for T { fn eq(&self, o: &T) -> bool { self.a == o.a } } \
             fn f(t: T) { assert!(t == t); }",
            "use dep::S; #[trust_vc::spec] fn f(s: S) -> bool { s == s }",
            "use dep::S; fn f(s: S) { proof_block! { assert(s == s); } }",
            "use dep::S; #[trust_vc::requires(s == s)] fn f(s: S) {}",
        ] {
            assert_eq!(refusal(src), None, "refused: {src}");
        }
    }

    #[test]
    fn the_message_names_the_function_and_the_tag() {
        let src = format!("{ROOT} fn f() {{ let a = r(); let b = r(); }}");
        let message = refusal(&src).expect("refused");
        assert!(message.starts_with(BODILESS_CALL_REPEAT_TAG), "{message}");
        assert!(message.contains("`r`"), "{message}");
    }
}
