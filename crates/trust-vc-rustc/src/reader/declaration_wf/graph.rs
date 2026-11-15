//! Bounded versions of pinned Verus's strict positivity and base-case checks.
//!
//! Types and graph nodes are private transient validation inputs. They are
//! discarded after checking and never supply a representation to the verifier.

use super::super::declaration_policy::Recursion;

const MAX_GRAPH_WORK: usize = 262_144;
const MAX_DEPTH: usize = 64;

/// Language failures carry graph-local original-owner indices. Missing facts,
/// malformed inputs and exhausted budgets remain unavailable evidence.
#[derive(Debug)]
pub(super) enum Failure {
    Unknown(String),
    NonPositiveDatatype { owner: usize, target: usize },
    NonPositiveParameter { owner: usize, parameter: u32 },
    NoBase { owners: Vec<usize> },
}

impl From<&str> for Failure {
    fn from(reason: &str) -> Self {
        Self::Unknown(reason.into())
    }
}

impl From<String> for Failure {
    fn from(reason: String) -> Self {
        Self::Unknown(reason)
    }
}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Unknown(reason) => reason,
            Self::NonPositiveDatatype { .. } => {
                "a datatype recursively uses an SCC member in a non-positive position"
            }
            Self::NonPositiveParameter { .. } => {
                "a non-positive parameter must declare reject_recursive_types"
            }
            Self::NoBase { .. } => "a datatype has no non-recursive base-case variant",
        })
    }
}

pub(super) enum Type {
    Base,
    Parameter(u32),
    Product(Vec<Type>),
    SpecFunction {
        inputs: Vec<Type>,
        output: Box<Type>,
    },
    Nominal {
        node: usize,
        arguments: Vec<Type>,
    },
    /// A use of an imported datatype whose original positivity and base case
    /// are already licensed. This is a policy summary, never a field layout or
    /// an empty variant inferred from an opaque IR declaration.
    Imported {
        parameters: Vec<Recursion>,
        arguments: Vec<Type>,
    },
    Decorated(Box<Type>),
}

pub(super) struct Declaration {
    pub(super) parameters: Vec<Recursion>,
    pub(super) variants: Vec<Vec<Type>>,
}

pub(super) struct Graph {
    pub(super) declarations: Vec<Declaration>,
}

struct Work(usize);
impl Work {
    fn charge(&mut self) -> Result<(), Failure> {
        self.0 = self
            .0
            .checked_sub(1)
            .ok_or("datatype validation exceeds its work bound")?;
        Ok(())
    }
    fn depth(&mut self, depth: usize) -> Result<(), Failure> {
        self.charge()?;
        if depth > MAX_DEPTH {
            Err("datatype validation exceeds its depth bound".into())
        } else {
            Ok(())
        }
    }
}

fn children(
    ty: &Type,
    edges: &mut Vec<usize>,
    work: &mut Work,
    depth: usize,
) -> Result<(), Failure> {
    work.depth(depth)?;
    match ty {
        Type::Base | Type::Parameter(_) => {}
        Type::Product(values) => {
            for value in values {
                children(value, edges, work, depth + 1)?;
            }
        }
        Type::SpecFunction { inputs, output } => {
            for input in inputs {
                children(input, edges, work, depth + 1)?;
            }
            children(output, edges, work, depth + 1)?;
        }
        Type::Nominal { node, arguments } => {
            edges.push(*node);
            for argument in arguments {
                children(argument, edges, work, depth + 1)?;
            }
        }
        Type::Imported {
            parameters,
            arguments,
        } => {
            if parameters.len() > 256 || parameters.len() != arguments.len() {
                return Err("imported datatype policy and argument arity disagree".into());
            }
            // An already-built dependency cannot refer to a new client's
            // local declarations. Every local edge is through its arguments.
            for argument in arguments {
                children(argument, edges, work, depth + 1)?;
            }
        }
        Type::Decorated(inner) => children(inner, edges, work, depth + 1)?,
    }
    Ok(())
}

fn positive(
    ty: &Type,
    owner: usize,
    polarity: bool,
    graph: &Graph,
    reachable: &[Vec<bool>],
    work: &mut Work,
    depth: usize,
) -> Result<(), Failure> {
    work.depth(depth)?;
    let declaration = &graph.declarations[owner];
    match ty {
        Type::Base => {}
        Type::Parameter(index) => {
            let policy = declaration
                .parameters
                .get(*index as usize)
                .ok_or("a datatype field parameter has no checked native binder")?;
            if *policy != Recursion::Reject && !polarity {
                return Err(Failure::NonPositiveParameter {
                    owner,
                    parameter: *index,
                });
            }
        }
        Type::Product(values) => {
            for value in values {
                positive(value, owner, polarity, graph, reachable, work, depth + 1)?;
            }
        }
        Type::SpecFunction { inputs, output } => {
            // Strict positivity: entering a function input never flips back to
            // positive through a second function input.
            for input in inputs {
                positive(input, owner, false, graph, reachable, work, depth + 1)?;
            }
            positive(output, owner, polarity, graph, reachable, work, depth + 1)?;
        }
        Type::Nominal { node, arguments } => {
            let target = graph
                .declarations
                .get(*node)
                .ok_or("an unknown datatype graph node")?;
            if arguments.len() != target.parameters.len() {
                return Err("datatype application arity differs from native policy".into());
            }
            if (owner == *node || (reachable[owner][*node] && reachable[*node][owner])) && !polarity
            {
                return Err(Failure::NonPositiveDatatype {
                    owner,
                    target: *node,
                });
            }
            for (argument, policy) in arguments.iter().zip(&target.parameters) {
                positive(
                    argument,
                    owner,
                    polarity && *policy != Recursion::Reject,
                    graph,
                    reachable,
                    work,
                    depth + 1,
                )?;
            }
        }
        Type::Imported {
            parameters,
            arguments,
        } => {
            if parameters.len() != arguments.len() {
                return Err("imported datatype application arity differs from its policy".into());
            }
            for (argument, policy) in arguments.iter().zip(parameters) {
                positive(
                    argument,
                    owner,
                    polarity && *policy != Recursion::Reject,
                    graph,
                    reachable,
                    work,
                    depth + 1,
                )?;
            }
        }
        Type::Decorated(inner) => {
            positive(inner, owner, polarity, graph, reachable, work, depth + 1)?
        }
    }
    Ok(())
}

fn ground(
    ty: &Type,
    owner: usize,
    graph: &Graph,
    founded: &[bool],
    work: &mut Work,
    depth: usize,
) -> Result<bool, Failure> {
    work.depth(depth)?;
    Ok(match ty {
        Type::Base => true,
        Type::Parameter(index) => {
            *graph.declarations[owner]
                .parameters
                .get(*index as usize)
                .ok_or("a base-case parameter has no checked native binder")?
                != Recursion::Accept
        }
        Type::Product(values) => {
            let mut all = true;
            for value in values {
                all &= ground(value, owner, graph, founded, work, depth + 1)?;
            }
            all
        }
        // Verus constructs a default constant function from a base-case result;
        // its input domains need not be inhabited.
        Type::SpecFunction { output, .. } => {
            ground(output, owner, graph, founded, work, depth + 1)?
        }
        Type::Nominal { node, arguments } => {
            let target = graph
                .declarations
                .get(*node)
                .ok_or("an unknown base-case datatype node")?;
            if target.parameters.len() != arguments.len() {
                return Err("base-case application arity differs from native policy".into());
            }
            if !founded[*node] {
                false
            } else {
                let mut all = true;
                for (argument, policy) in arguments.iter().zip(&target.parameters) {
                    if *policy != Recursion::Accept {
                        all &= ground(argument, owner, graph, founded, work, depth + 1)?;
                    }
                }
                all
            }
        }
        Type::Imported {
            parameters,
            arguments,
        } => {
            if parameters.len() != arguments.len() {
                return Err("imported base-case application arity differs from its policy".into());
            }
            // The imported carrier's own base case was checked in its source
            // context. Reject and RejectInGround still need founded arguments;
            // Accept alone permits an argument without a ground inhabitant.
            let mut all = true;
            for (argument, policy) in arguments.iter().zip(parameters) {
                if *policy != Recursion::Accept {
                    all &= ground(argument, owner, graph, founded, work, depth + 1)?;
                }
            }
            all
        }
        Type::Decorated(inner) => ground(inner, owner, graph, founded, work, depth + 1)?,
    })
}

pub(super) fn validate(graph: &Graph) -> Result<(), Failure> {
    if graph.declarations.is_empty() || graph.declarations.len() > 256 {
        return Err("datatype graph inventory is empty or exceeds its bound".into());
    }
    let mut work = Work(MAX_GRAPH_WORK);
    let count = graph.declarations.len();
    let mut edges = Vec::new();
    for declaration in &graph.declarations {
        let mut row = Vec::new();
        for variant in &declaration.variants {
            work.charge()?;
            for ty in variant {
                children(ty, &mut row, &mut work, 0)?;
            }
        }
        if row.iter().any(|target| *target >= count) {
            return Err("datatype graph contains an unknown node".into());
        }
        row.sort_unstable();
        row.dedup();
        edges.push(row);
    }
    let mut reachable = vec![vec![false; count]; count];
    for (start, seen) in reachable.iter_mut().enumerate() {
        let mut pending = edges[start].clone();
        while let Some(node) = pending.pop() {
            work.charge()?;
            if !seen[node] {
                seen[node] = true;
                pending.extend(edges[node].iter().copied());
            }
        }
    }
    for (owner, declaration) in graph.declarations.iter().enumerate() {
        for variant in &declaration.variants {
            for ty in variant {
                positive(ty, owner, true, graph, &reachable, &mut work, 0)?;
            }
        }
    }
    // Least fixed point of available base variants. No cycle can bootstrap its
    // own inhabitants, and a parameter marked Accept cannot serve as a base.
    let mut founded = vec![false; count];
    loop {
        let mut changed = false;
        for (owner, declaration) in graph.declarations.iter().enumerate() {
            if founded[owner] {
                continue;
            }
            for variant in &declaration.variants {
                work.charge()?;
                let mut all = true;
                for ty in variant {
                    all &= ground(ty, owner, graph, &founded, &mut work, 0)?;
                }
                if all {
                    founded[owner] = true;
                    changed = true;
                    break;
                }
            }
        }
        if founded.iter().all(|value| *value) {
            return Ok(());
        }
        if !changed {
            // Capture order is not Verus's dependency-SCC diagnostic order.
            // Preserve the complete failure set for the native reader's
            // existing ordering pass rather than selecting a guessed primary.
            let owners = founded
                .iter()
                .enumerate()
                .filter_map(|(owner, value)| (!*value).then_some(owner))
                .collect();
            return Err(Failure::NoBase { owners });
        }
    }
}
