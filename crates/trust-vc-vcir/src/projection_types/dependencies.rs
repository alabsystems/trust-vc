//! Program-structure closure for the new closed associated semantics.
//! Collect raw fields and complete implementation arguments before reducing
//! their projections. Native graph receipts/flags never stand in for this.

use super::*;

#[derive(Clone, PartialEq, Eq, Hash)]
enum Node {
    Member(ProjectionId, Vec<Ty>),
    Datatype(AdtId, Vec<Ty>),
}

impl Node {
    fn price(&self, work: &mut usize) -> Option<()> {
        let args = match self { Self::Member(_, args) | Self::Datatype(_, args) => args };
        charge(work, 1 + args.len())?;
        for ty in args { crate::instance_semantics::price_type(ty, work)?; }
        Some(())
    }
    fn copy(&self, work: &mut usize) -> Option<Self> { self.price(work)?; Some(self.clone()) }
}

fn arguments(definitions: &Definitions<'_>, args: &[Ty], work: &mut usize) -> Option<Vec<Ty>> {
    charge(work, args.len())?;
    args.iter().map(|ty| definitions.normalize(ty, work)).collect()
}

fn references(definitions: &Definitions<'_>, ty: &Ty, edges: &mut Vec<Node>, work: &mut usize) -> Option<()> {
    charge(work, 1)?;
    let mut pending = vec![(ty, 0usize)];
    while let Some((ty, depth)) = pending.pop() {
        charge(work, 1)?;
        if depth >= 64 { return None; }
        match ty {
            Ty::Adt(_, args) | Ty::Projection(_, args) => {
                charge(work, args.len())?;
                // Dependencies in arguments also survive normalization.
                pending.extend(args.iter().map(|ty| (ty, depth + 1)));
                let args = arguments(definitions, args, work)?;
                charge(work, 1)?;
                edges.push(match ty {
                    Ty::Adt(id, _) => Node::Datatype(*id, args),
                    Ty::Projection(id, _) => {
                        definitions.lookup(*id, &args, work)??;
                        Node::Member(*id, args)
                    }
                    _ => return None,
                });
            }
            Ty::Tuple(args) => {
                charge(work, args.len())?;
                pending.extend(args.iter().map(|ty| (ty, depth + 1)));
            }
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => { charge(work, 1)?; pending.push((inner, depth + 1)); }
            Ty::Bool | Ty::Int(_) | Ty::Unit => {}
            Ty::Param(_) => return None,
        }
    }
    Some(())
}

pub(super) fn check(definitions: &Definitions<'_>, source: &VcCrate, work: &mut usize) -> Option<()> {
    if source.projection_impls.is_empty() { return Some(()); }
    charge(work, source.adts.len())?;
    let adts: HashMap<_, _> = source.adts.iter().map(|adt| (adt.id, adt)).collect();
    let mut roots = Vec::new();
    let mut pending = Vec::new();
    for implementation in &source.projection_impls {
        for value in &implementation.values {
            let root = Node::Member(value.declaration, arguments(definitions, &implementation.arguments, work)?);
            charge(work, 2)?;
            pending.push(root.copy(work)?);
            roots.push(root);
        }
    }
    let mut graph: HashMap<Node, Vec<Node>> = HashMap::new();
    while let Some(node) = pending.pop() {
        node.price(work)?;
        if graph.contains_key(&node) { continue; }
        let mut edges = Vec::new();
        match &node {
            Node::Member(member, args) => {
                for argument in args { references(definitions, argument, &mut edges, work)?; }
                let value = definitions.lookup(*member, args, work)??;
                references(definitions, value, &mut edges, work)?;
            }
            Node::Datatype(id, args) => {
                let declaration = adts.get(id)?;
                if declaration.type_params.len() != args.len() { return None; }
                for variant in &declaration.variants {
                    for field in &variant.fields {
                        let raw = definitions.raw_substitute(&field.ty, Some(args), work, 0)?;
                        references(definitions, &raw, &mut edges, work)?;
                    }
                }
            }
        }
        charge(work, edges.len())?;
        for edge in &edges { pending.push(edge.copy(work)?); }
        node.price(work)?;
        graph.insert(node, edges);
    }
    // Only cycles through the new associated semantics are new refusals.
    // Datatype-only recursion retains the existing representation policy.
    for root in roots {
        root.price(work)?;
        let mut pending = Vec::new();
        for edge in graph.get(&root)? { pending.push(edge.copy(work)?); }
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            node.price(work)?;
            root.price(work)?;
            if node == root { return None; }
            node.price(work)?;
            if !seen.insert(node.copy(work)?) { continue; }
            node.price(work)?;
            for edge in graph.get(&node)? { pending.push(edge.copy(work)?); }
        }
    }
    Some(())
}
