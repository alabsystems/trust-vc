// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ---------------------------------------------------------------------------
// Difficulty estimation
// ---------------------------------------------------------------------------

/// Factors contributing to estimated solving difficulty.
#[derive(Debug, Clone)]
pub struct DifficultyFactor {
    /// Factor name.
    pub name: String,
    /// Contribution to the total score (may be negative for mitigating factors).
    pub contribution: f64,
    /// Brief explanation.
    pub explanation: String,
}

/// Estimated difficulty report for a VC.
#[derive(Debug, Clone)]
pub struct DifficultyReport {
    /// Aggregate difficulty score in `[0, +inf)`.
    pub score: f64,
    /// Human-readable difficulty label.
    pub label: DifficultyLabel,
    /// Factors that contributed to the score.
    pub factors: Vec<DifficultyFactor>,
    /// Recommended solver configuration hints.
    pub recommendations: Vec<String>,
}

/// Coarse difficulty labels for human consumption.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum DifficultyLabel {
    Trivial,
    Easy,
    Moderate,
    Hard,
    VeryHard,
}

impl DifficultyLabel {
    pub fn from_score(score: f64) -> Self {
        if score < 5.0 {
            Self::Trivial
        } else if score < 20.0 {
            Self::Easy
        } else if score < 50.0 {
            Self::Moderate
        } else if score < 100.0 {
            Self::Hard
        } else {
            Self::VeryHard
        }
    }
}

/// Estimates solving difficulty from a `VcAnalysis`.
pub struct DifficultyEstimator;

impl DifficultyEstimator {
    /// Produce a difficulty report from a complete analysis.
    #[must_use]
    pub fn estimate(analysis: &VcAnalysis) -> DifficultyReport {
        let mut factors = Vec::new();
        let mut score = 0.0_f64;

        // Quantifier cost.
        let qp = &analysis.quantifier_profile;
        if qp.count > 0 {
            let q_score = 10.0 + qp.max_depth as f64 * 8.0 + qp.count as f64 * 3.0;
            score += q_score;
            factors.push(DifficultyFactor {
                name: "quantifiers".into(),
                contribution: q_score,
                explanation: format!(
                    "{} quantifiers, max depth {}, {} alternations",
                    qp.count, qp.max_depth, qp.alternation_count
                ),
            });
        }

        // Alternation penalty.
        if qp.alternation_count > 0 {
            let alt_score = qp.alternation_count as f64 * 15.0;
            score += alt_score;
            factors.push(DifficultyFactor {
                name: "quantifier_alternation".into(),
                contribution: alt_score,
                explanation: format!(
                    "{} alternations (forall/exists transitions)",
                    qp.alternation_count
                ),
            });
        }

        // Arithmetic cost.
        let ap = &analysis.arith_profile;
        if ap.has_nonlinear {
            let nl_score = 25.0 + ap.op_count as f64 * 0.5;
            score += nl_score;
            factors.push(DifficultyFactor {
                name: "nonlinear_arithmetic".into(),
                contribution: nl_score,
                explanation: format!("{} arithmetic ops with nonlinear terms", ap.op_count),
            });
        } else if ap.has_linear {
            let l_score = 5.0 + ap.op_count as f64 * 0.1;
            score += l_score;
            factors.push(DifficultyFactor {
                name: "linear_arithmetic".into(),
                contribution: l_score,
                explanation: format!("{} linear arithmetic ops", ap.op_count),
            });
        }

        // Bitvector cost.
        let bp = &analysis.bv_profile;
        if bp.op_count > 0 {
            let bv_score = 8.0 + (bp.max_width as f64 / 16.0).min(20.0) + bp.op_count as f64 * 0.3;
            score += bv_score;
            factors.push(DifficultyFactor {
                name: "bitvectors".into(),
                contribution: bv_score,
                explanation: format!(
                    "{} BV ops, max width {}, shift={}, rotate={}",
                    bp.op_count, bp.max_width, bp.has_shift, bp.has_rotate
                ),
            });
        }

        // Array/sequence cost.
        if analysis.statistics.array_op_count > 0 {
            let arr_score = 7.0 + analysis.statistics.array_op_count as f64 * 0.5;
            score += arr_score;
            factors.push(DifficultyFactor {
                name: "arrays".into(),
                contribution: arr_score,
                explanation: format!("{} array/sequence ops", analysis.statistics.array_op_count),
            });
        }

        // UF cost.
        if analysis.statistics.uf_app_count > 0 {
            let uf_score = 3.0 + analysis.statistics.uf_app_count as f64 * 1.5;
            score += uf_score;
            factors.push(DifficultyFactor {
                name: "uninterpreted_functions".into(),
                contribution: uf_score,
                explanation: format!("{} UF applications", analysis.statistics.uf_app_count),
            });
        }

        // Size cost.
        let size_score = analysis.statistics.node_count as f64 * 0.02
            + analysis.statistics.variable_count as f64 * 0.1;
        if size_score > 1.0 {
            score += size_score;
            factors.push(DifficultyFactor {
                name: "size".into(),
                contribution: size_score,
                explanation: format!(
                    "{} nodes, {} variables",
                    analysis.statistics.node_count, analysis.statistics.variable_count
                ),
            });
        }

        // Build recommendations.
        let mut recommendations = Vec::new();
        if qp.count > 5 {
            recommendations.push("Consider increasing E-matching rounds".into());
        }
        if qp.alternation_count > 0 {
            recommendations.push("Enable MBQI for quantifier alternation".into());
        }
        if ap.has_nonlinear {
            recommendations.push("Use NIA-specialized solver mode".into());
        }
        if bp.op_count > 0 && bp.max_width >= 64 {
            recommendations.push("Use BV-focused strategy with eager theory combination".into());
        }
        if analysis.statistics.node_count > 1000 {
            recommendations.push("Apply per-assertion SMT pruning".into());
        }
        if analysis
            .patterns
            .iter()
            .any(|p| p.name == "division_safety")
        {
            recommendations.push("Enable division-by-zero guard preprocessing".into());
        }

        let label = DifficultyLabel::from_score(score);

        DifficultyReport {
            score,
            label,
            factors,
            recommendations,
        }
    }
}
