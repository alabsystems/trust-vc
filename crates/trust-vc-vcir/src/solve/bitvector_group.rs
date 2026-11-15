//! Execute one original isolated assertion in architecture-major order.
//! Admission of every clause/case is completed before any native query. Every
//! genuine per-width answer is retained. The reporter counts each source clause
//! once; Unknown/Error remain refusal events even beside a real refutation.

#[cfg(test)]
use super::Term;
use super::{admit_complete, check_detailed, DetailedVerdict, Limits, Query};

/// Results in actual execution order, with original indices into `clauses`.
/// These are case events, not additional source sites. A caller must aggregate
/// source counts once and retain every Unknown/Error refusal event.
pub fn check_bitvector_group(
    clauses: &[(&Query, &str)],
    limits: &Limits,
) -> Result<Vec<(usize, DetailedVerdict)>, String> {
    check_with(clauses, limits, check_detailed)
}

fn case(query: &Query, pass: usize) -> Option<(u32, &Query)> {
    if let Some(cases) = &query.architectures {
        cases.get(pass).map(|(width, case)| (*width, case))
    } else if pass == 0 {
        query
            .bitvector
            .as_ref()
            .and_then(|cases| (cases.len() == 1).then(|| (cases[0].architecture, query)))
    } else {
        None
    }
}

fn check_with(
    clauses: &[(&Query, &str)],
    limits: &Limits,
    mut solve: impl FnMut(&Query, &str, &Limits) -> DetailedVerdict,
) -> Result<Vec<(usize, DetailedVerdict)>, String> {
    if clauses.is_empty() || clauses.len() > 200_000 {
        return Err("an empty or oversized isolated BV assertion group".into());
    }
    let first_widths: Vec<_> = (0..2)
        .filter_map(|pass| case(clauses[0].0, pass).map(|c| c.0))
        .collect();
    for (query, label) in clauses {
        admit_complete(query, label)?;
        let widths: Vec<_> = (0..2)
            .filter_map(|pass| case(query, pass).map(|c| c.0))
            .collect();
        if widths.is_empty() || widths != first_widths {
            return Err("inconsistent architecture cases in an isolated BV assertion group".into());
        }
        for pass in 0..widths.len() {
            let (_, child) = case(query, pass).ok_or("missing isolated BV group case")?;
            // This API answers isolated obligations, not ordinary dead-path
            // checks. A true placeholder cannot stand in for an omitted BV
            // source event, including a width whose outer branch returned.
            if child.bitvector.is_none() {
                return Err("a required isolated BV architecture case is missing".into());
            }
        }
    }
    let mut out = Vec::with_capacity(clauses.len() * first_widths.len());
    for pass in 0..first_widths.len() {
        for (index, (query, label)) in clauses.iter().enumerate() {
            let (width, child) = case(query, pass).ok_or("missing admitted BV group case")?;
            let qualified = if query.architectures.is_some() {
                format!("{label}_arch{width}")
            } else {
                (*label).to_owned()
            };
            let result = solve(child, &qualified, limits);
            out.push((index, result));
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests;
