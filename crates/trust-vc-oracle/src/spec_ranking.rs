// trust-vc-oracle — Specification ranking and scoring
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Ranks mined specs by a composite score considering verification status,
// refinement count, template specificity, and spec strength.

use crate::mining::MinedSpec;

// ---------------------------------------------------------------------------
// Score components and weights
// ---------------------------------------------------------------------------

/// Weights for each scoring dimension.
///
/// Public for transparency/testing. The composite score is the weighted
/// sum of normalised component scores.
pub mod weights {
    /// Bonus for being verified (0 or 1, multiplied by this weight).
    pub const VERIFIED: f64 = 50.0;
    /// Maximum penalty for high iteration/refinement count.
    pub const REFINEMENT: f64 = 20.0;
    /// Maximum bonus for template specificity.
    pub const SPECIFICITY: f64 = 20.0;
    /// Maximum penalty for many preconditions (spec weakness).
    pub const STRENGTH: f64 = 10.0;
}

/// Template specificity tiers.
///
/// Higher-specificity templates produce stronger, more informative specs.
/// These scores are normalised to `[0, 1]` and scaled by
/// `weights::SPECIFICITY`.
///
/// Ordering rationale:
///   - Structural templates (sorted, permutation, injective) are the most
///     specific because they constrain output structure.
///   - Algebraic templates (commutativity, associativity, distributivity)
///     are next — they describe function-level algebraic laws.
///   - Semantic templates (idempotent, identity, monotonic, invariant,
///     error_free) constrain behavior but not structure.
///   - Bound templates (range, bounded_by_input, non_negative,
///     preserves_property, length_preserving) are the most generic.
#[must_use]
pub fn template_specificity(template_name: &str) -> f64 {
    match template_name {
        // Tier 4 (most specific) — structural
        "sorted" => 1.0,
        "permutation" => 0.95,
        "injective" => 0.90,

        // Tier 3 — algebraic
        "commutativity" => 0.80,
        "associativity" => 0.75,
        "distributivity" => 0.70,

        // Tier 2 — semantic
        "idempotent" => 0.60,
        "identity" => 0.55,
        "monotonic" => 0.50,
        "invariant" => 0.45,
        "error_free" => 0.40,

        // Tier 1 (least specific) — bounds
        "range" => 0.30,
        "bounded_by_input" => 0.25,
        "non_negative" => 0.20,
        "preserves_property" => 0.15,
        "length_preserving" => 0.10,

        // Unknown templates get minimal specificity.
        _ => 0.05,
    }
}

// ---------------------------------------------------------------------------
// SpecScore
// ---------------------------------------------------------------------------

/// Breakdown of how a spec's composite score was computed.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct SpecScore {
    /// Composite score (higher is better).
    pub score: f64,
    /// Confidence in `[0, 1]`: 1.0 when all components are unambiguous.
    pub confidence: f64,
    /// Individual score components for explainability.
    pub components: ScoreComponents,
}

/// Individual score components.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub struct ScoreComponents {
    /// Verification bonus (0.0 or `weights::VERIFIED`).
    pub verified: f64,
    /// Refinement score — lower iterations is better.
    pub refinement: f64,
    /// Template specificity score.
    pub specificity: f64,
    /// Spec strength score — fewer preconditions is stronger.
    pub strength: f64,
}

// ---------------------------------------------------------------------------
// RankedSpec
// ---------------------------------------------------------------------------

/// A mined spec together with its computed rank and score.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct RankedSpec {
    /// The underlying mined spec (cloned for ownership).
    pub spec: MinedSpec,
    /// Composite score and breakdown.
    pub score: SpecScore,
    /// 1-based rank (1 = best).
    pub rank: usize,
    /// Human-readable explanation of the ranking.
    pub explanation: String,
}

// ---------------------------------------------------------------------------
// Scoring
// ---------------------------------------------------------------------------

/// Compute the composite score for a single mined spec.
#[must_use]
pub fn score_spec(spec: &MinedSpec) -> SpecScore {
    // Verified component: binary.
    let verified_component = if spec.verified {
        weights::VERIFIED
    } else {
        0.0
    };

    // Refinement component: 0 iterations = full score, 5+ = 0.
    let max_iterations_for_scoring = 5.0_f64;
    let iteration_ratio = 1.0 - (spec.iterations as f64 / max_iterations_for_scoring).min(1.0);
    let refinement_component = iteration_ratio * weights::REFINEMENT;

    // Specificity component.
    let specificity_raw = template_specificity(&spec.template_name);
    let specificity_component = specificity_raw * weights::SPECIFICITY;

    // Strength component: more requires = weaker spec = lower score.
    // 0 requires = full score, 3+ requires = 0.
    let max_requires_for_scoring = 3.0_f64;
    let strength_ratio = 1.0 - (spec.requires.len() as f64 / max_requires_for_scoring).min(1.0);
    let strength_component = strength_ratio * weights::STRENGTH;

    let score =
        verified_component + refinement_component + specificity_component + strength_component;

    // Confidence: 1.0 when verified, reduced when unverified.
    let confidence = if spec.verified { 1.0 } else { 0.3 };

    SpecScore {
        score,
        confidence,
        components: ScoreComponents {
            verified: verified_component,
            refinement: refinement_component,
            specificity: specificity_component,
            strength: strength_component,
        },
    }
}

// ---------------------------------------------------------------------------
// Ranking
// ---------------------------------------------------------------------------

/// Rank a set of mined specs by composite score (descending).
///
/// Returns a new `Vec<RankedSpec>` with 1-based ranks. Ties receive the
/// same score but sequential rank numbers.
#[must_use]
pub fn rank_specs(specs: &[MinedSpec]) -> Vec<RankedSpec> {
    let mut scored: Vec<(MinedSpec, SpecScore)> =
        specs.iter().map(|s| (s.clone(), score_spec(s))).collect();

    // Sort descending by score.
    scored.sort_by(|a, b| {
        b.1.score
            .partial_cmp(&a.1.score)
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    scored
        .into_iter()
        .enumerate()
        .map(|(i, (spec, score))| {
            let rank = i + 1;
            let explanation = format_explanation(&spec, &score, rank);
            RankedSpec {
                spec,
                score,
                rank,
                explanation,
            }
        })
        .collect()
}

/// Generate a human-readable explanation for a ranking.
fn format_explanation(spec: &MinedSpec, score: &SpecScore, rank: usize) -> String {
    let status = if spec.verified {
        "verified"
    } else {
        "unverified"
    };
    format!(
        "#{rank}: {fn_name}::{tmpl} ({status}, {iter} iterations, score={score:.1}) \
         [verified={v:.0} refinement={r:.1} specificity={s:.1} strength={st:.1}]",
        fn_name = spec.function_name,
        tmpl = spec.template_name,
        iter = spec.iterations,
        score = score.score,
        v = score.components.verified,
        r = score.components.refinement,
        s = score.components.specificity,
        st = score.components.strength,
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_spec(
        func: &str,
        template: &str,
        verified: bool,
        iterations: usize,
        requires_count: usize,
    ) -> MinedSpec {
        MinedSpec::new(
            func.to_string(),
            template.to_string(),
            (0..requires_count).map(|i| format!("x > {i}")).collect(),
            vec!["result >= 0".to_string()],
            verified,
            iterations,
        )
    }

    // -----------------------------------------------------------------------
    // Template specificity ordering
    // -----------------------------------------------------------------------

    #[test]
    fn test_specificity_sorted_highest() {
        assert!(template_specificity("sorted") > template_specificity("range"));
        assert!(template_specificity("sorted") > template_specificity("monotonic"));
        assert!(template_specificity("sorted") > template_specificity("commutativity"));
    }

    #[test]
    fn test_specificity_permutation_above_range() {
        assert!(template_specificity("permutation") > template_specificity("range"));
    }

    #[test]
    fn test_specificity_range_above_non_negative() {
        assert!(template_specificity("range") > template_specificity("non_negative"));
    }

    #[test]
    fn test_specificity_algebraic_above_semantic() {
        assert!(template_specificity("commutativity") > template_specificity("idempotent"));
        assert!(template_specificity("associativity") > template_specificity("identity"));
    }

    #[test]
    fn test_specificity_unknown_template_gets_minimum() {
        let unknown = template_specificity("unknown_template_xyz");
        assert!(unknown < template_specificity("length_preserving"));
        assert!(unknown > 0.0);
    }

    #[test]
    fn test_specificity_all_templates_in_zero_one() {
        let templates = [
            "sorted",
            "permutation",
            "injective",
            "commutativity",
            "associativity",
            "distributivity",
            "idempotent",
            "identity",
            "monotonic",
            "invariant",
            "error_free",
            "range",
            "bounded_by_input",
            "non_negative",
            "preserves_property",
            "length_preserving",
        ];
        for t in &templates {
            let s = template_specificity(t);
            assert!(s > 0.0 && s <= 1.0, "{t}: specificity={s} out of range");
        }
    }

    // -----------------------------------------------------------------------
    // Score components
    // -----------------------------------------------------------------------

    #[test]
    fn test_score_verified_bonus() {
        let verified = score_spec(&make_spec("f", "range", true, 0, 0));
        let unverified = score_spec(&make_spec("f", "range", false, 0, 0));
        assert!(verified.score > unverified.score);
        assert_eq!(verified.components.verified, weights::VERIFIED);
        assert_eq!(unverified.components.verified, 0.0);
    }

    #[test]
    fn test_score_fewer_iterations_better() {
        let zero = score_spec(&make_spec("f", "range", true, 0, 0));
        let three = score_spec(&make_spec("f", "range", true, 3, 0));
        assert!(
            zero.score > three.score,
            "0 iterations should score higher than 3"
        );
    }

    #[test]
    fn test_score_high_iterations_floors_at_zero_refinement() {
        let five = score_spec(&make_spec("f", "range", true, 5, 0));
        let ten = score_spec(&make_spec("f", "range", true, 10, 0));
        assert_eq!(five.components.refinement, 0.0);
        assert_eq!(ten.components.refinement, 0.0);
    }

    #[test]
    fn test_score_fewer_requires_stronger() {
        let no_req = score_spec(&make_spec("f", "range", true, 0, 0));
        let many_req = score_spec(&make_spec("f", "range", true, 0, 3));
        assert!(
            no_req.score > many_req.score,
            "0 requires should score higher than 3"
        );
        assert_eq!(many_req.components.strength, 0.0);
    }

    #[test]
    fn test_score_specificity_higher_for_sorted() {
        let sorted = score_spec(&make_spec("f", "sorted", true, 0, 0));
        let range = score_spec(&make_spec("f", "range", true, 0, 0));
        assert!(sorted.components.specificity > range.components.specificity);
    }

    #[test]
    fn test_score_confidence_verified_is_one() {
        let s = score_spec(&make_spec("f", "range", true, 0, 0));
        assert_eq!(s.confidence, 1.0);
    }

    #[test]
    fn test_score_confidence_unverified_is_low() {
        let s = score_spec(&make_spec("f", "range", false, 0, 0));
        assert!(s.confidence < 1.0);
    }

    // -----------------------------------------------------------------------
    // Ranking
    // -----------------------------------------------------------------------

    #[test]
    fn test_rank_specs_descending_order() {
        let specs = vec![
            make_spec("f", "range", false, 3, 2),
            make_spec("f", "sorted", true, 0, 0),
            make_spec("f", "non_negative", true, 1, 1),
        ];
        let ranked = rank_specs(&specs);
        assert_eq!(ranked.len(), 3);
        assert_eq!(ranked[0].rank, 1);
        assert_eq!(ranked[0].spec.template_name, "sorted");
        assert!(ranked[0].score.score >= ranked[1].score.score);
        assert!(ranked[1].score.score >= ranked[2].score.score);
    }

    #[test]
    fn test_rank_specs_empty_input() {
        let ranked = rank_specs(&[]);
        assert!(ranked.is_empty());
    }

    #[test]
    fn test_rank_specs_single_spec() {
        let specs = vec![make_spec("f", "range", true, 0, 0)];
        let ranked = rank_specs(&specs);
        assert_eq!(ranked.len(), 1);
        assert_eq!(ranked[0].rank, 1);
    }

    #[test]
    fn test_rank_specs_verified_always_above_unverified() {
        let specs = vec![
            make_spec("f", "sorted", false, 0, 0),
            make_spec("f", "length_preserving", true, 5, 3),
        ];
        let ranked = rank_specs(&specs);
        // The verified length_preserving should rank above the unverified sorted
        // even though sorted has better specificity.
        assert!(ranked[0].spec.verified);
        assert!(!ranked[1].spec.verified);
    }

    #[test]
    fn test_rank_specs_explanation_contains_key_info() {
        let specs = vec![make_spec("myfn", "range", true, 2, 1)];
        let ranked = rank_specs(&specs);
        let exp = &ranked[0].explanation;
        assert!(
            exp.contains("myfn"),
            "explanation should contain function name"
        );
        assert!(
            exp.contains("range"),
            "explanation should contain template name"
        );
        assert!(
            exp.contains("verified"),
            "explanation should contain status"
        );
        assert!(exp.contains("#1"), "explanation should contain rank");
    }

    #[test]
    fn test_rank_specs_preserves_all_specs() {
        let specs = vec![
            make_spec("a", "range", true, 0, 0),
            make_spec("b", "sorted", true, 0, 0),
            make_spec("c", "identity", false, 2, 1),
        ];
        let ranked = rank_specs(&specs);
        assert_eq!(ranked.len(), 3);
        let names: Vec<&str> = ranked
            .iter()
            .map(|r| r.spec.function_name.as_str())
            .collect();
        assert!(names.contains(&"a"));
        assert!(names.contains(&"b"));
        assert!(names.contains(&"c"));
    }
}
