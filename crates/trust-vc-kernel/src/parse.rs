// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Text parser and formatter for ay-dpll UNSAT proof traces.

use std::collections::BTreeMap;

use thiserror::Error;

use crate::types::{Clause, ClauseId, LiteralId, ProofTrace, ResolutionStep, TheoryLemma};

const INPUT_RECORD_USAGE: &str = "i <clause_id> <lit1> <lit2> ... 0";
const THEORY_RECORD_USAGE: &str = "t <clause_id> <theory_name> <lit1> <lit2> ... 0";
const RESOLUTION_RECORD_USAGE: &str =
    "r <result_id> <pivot> <parent1> <parent2> [<lit1> <lit2> ... 0]";
const EMPTY_RECORD_USAGE: &str = "e <clause_id>";

/// Errors that can occur while parsing a text proof trace.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum ParseError {
    /// The line does not match any supported record type.
    #[error("line {line}: unrecognized record `{content}`")]
    UnrecognizedRecord { line: usize, content: String },

    /// The record has the wrong number of fields.
    #[error(
        "line {line}: malformed {record} record, expected `{expected}`, found {found} field(s)"
    )]
    InvalidFieldCount {
        line: usize,
        record: &'static str,
        expected: &'static str,
        found: usize,
    },

    /// A clause identifier token was invalid.
    #[error("line {line}: invalid clause id `{value}`")]
    InvalidClauseId { line: usize, value: String },

    /// A literal token was invalid.
    #[error("line {line}: invalid literal `{value}`")]
    InvalidLiteral { line: usize, value: String },

    /// A clause literal list is missing its terminating zero.
    #[error("line {line}: missing clause terminator `0`")]
    MissingClauseTerminator { line: usize },

    /// The terminator appeared before the end of the line.
    #[error("line {line}: clause terminator `0` must be the last token")]
    ClauseTerminatorNotLast { line: usize },

    /// Zero is not a valid literal inside a clause.
    #[error("line {line}: literal `{value}` is invalid inside a clause")]
    ZeroLiteral { line: usize, value: String },

    /// Zero is not a valid pivot literal.
    #[error("line {line}: resolution pivot cannot be `0`")]
    ZeroPivot { line: usize },

    /// A clause-producing record reused an existing identifier.
    #[error("line {line}: duplicate clause id {id} (first defined on line {previous_line})")]
    DuplicateClauseId {
        line: usize,
        previous_line: usize,
        id: ClauseId,
    },

    /// The proof declared the empty clause multiple times.
    #[error("line {line}: duplicate empty clause marker (first declared on line {previous_line})")]
    DuplicateEmptyClause { line: usize, previous_line: usize },

    /// No empty clause marker was provided.
    #[error("missing empty clause marker: expected `{EMPTY_RECORD_USAGE}`")]
    MissingEmptyClause,

    /// The empty clause marker references an unknown identifier.
    #[error("line {line}: empty clause id {id} does not refer to a defined clause")]
    UnknownEmptyClauseId { line: usize, id: ClauseId },
}

/// Parse a ay-dpll proof trace from the line-based text format.
#[must_use = "parsed proof trace should be used"]
pub fn parse_proof_trace(input: &str) -> Result<ProofTrace, ParseError> {
    let mut input_clauses = Vec::new();
    let mut resolution_steps = Vec::new();
    let mut theory_lemmas = Vec::new();
    let mut seen_clause_ids = BTreeMap::new();
    let mut empty_clause = None;

    for (index, raw_line) in input.lines().enumerate() {
        let line = index + 1;

        if raw_line.trim().is_empty() || raw_line.starts_with("c ") {
            continue;
        }

        if raw_line.starts_with("i ") {
            let clause = parse_input_clause(raw_line, line, &mut seen_clause_ids)?;
            input_clauses.push(clause);
            continue;
        }

        if raw_line.starts_with("t ") {
            let lemma = parse_theory_lemma(raw_line, line, &mut seen_clause_ids)?;
            theory_lemmas.push(lemma);
            continue;
        }

        if raw_line.starts_with("r ") {
            let step = parse_resolution_step(raw_line, line, &mut seen_clause_ids)?;
            resolution_steps.push(step);
            continue;
        }

        if raw_line.starts_with("e ") {
            if let Some((previous_line, _)) = empty_clause {
                return Err(ParseError::DuplicateEmptyClause {
                    line,
                    previous_line,
                });
            }

            let tokens: Vec<&str> = raw_line.split_ascii_whitespace().collect();
            if tokens.len() != 2 {
                return Err(ParseError::InvalidFieldCount {
                    line,
                    record: "empty clause",
                    expected: EMPTY_RECORD_USAGE,
                    found: tokens.len(),
                });
            }

            let clause_id = parse_clause_id(tokens[1], line)?;
            empty_clause = Some((line, clause_id));
            continue;
        }

        return Err(ParseError::UnrecognizedRecord {
            line,
            content: raw_line.to_string(),
        });
    }

    let (empty_clause_line, empty_clause_id) =
        empty_clause.ok_or(ParseError::MissingEmptyClause)?;
    if !seen_clause_ids.contains_key(&empty_clause_id) {
        return Err(ParseError::UnknownEmptyClauseId {
            line: empty_clause_line,
            id: empty_clause_id,
        });
    }

    Ok(ProofTrace {
        input_clauses,
        resolution_steps,
        theory_lemmas,
        empty_clause_id,
    })
}

/// Format a proof trace back into the canonical text representation.
#[must_use]
pub fn format_proof_trace(trace: &ProofTrace) -> String {
    let mut out = String::new();

    for clause in &trace.input_clauses {
        append_clause_record(&mut out, "i", clause.id, None, &clause.literals);
    }

    for lemma in &trace.theory_lemmas {
        append_clause_record(
            &mut out,
            "t",
            lemma.id,
            Some(&lemma.theory),
            &lemma.clause.literals,
        );
    }

    for step in &trace.resolution_steps {
        out.push_str("r ");
        out.push_str(&step.id.to_string());
        out.push(' ');
        out.push_str(&step.pivot.to_string());
        out.push(' ');
        out.push_str(&step.parent1.to_string());
        out.push(' ');
        out.push_str(&step.parent2.to_string());
        if let Some(result_literals) = &step.result_literals {
            for literal in result_literals {
                out.push(' ');
                out.push_str(&literal.to_string());
            }
            out.push_str(" 0");
        }
        out.push('\n');
    }

    out.push_str("e ");
    out.push_str(&trace.empty_clause_id.to_string());
    out.push('\n');

    out
}

pub(crate) fn parse_input_clause(
    raw_line: &str,
    line: usize,
    seen_clause_ids: &mut BTreeMap<ClauseId, usize>,
) -> Result<Clause, ParseError> {
    let tokens: Vec<&str> = raw_line.split_ascii_whitespace().collect();
    if tokens.len() < 3 {
        return Err(ParseError::InvalidFieldCount {
            line,
            record: "input clause",
            expected: INPUT_RECORD_USAGE,
            found: tokens.len(),
        });
    }

    let id = parse_clause_id(tokens[1], line)?;
    record_clause_id(seen_clause_ids, id, line)?;
    let literals = parse_clause_literals(&tokens[2..], line)?;

    Ok(Clause { id, literals })
}

pub(crate) fn parse_theory_lemma(
    raw_line: &str,
    line: usize,
    seen_clause_ids: &mut BTreeMap<ClauseId, usize>,
) -> Result<TheoryLemma, ParseError> {
    let tokens: Vec<&str> = raw_line.split_ascii_whitespace().collect();
    if tokens.len() < 4 {
        return Err(ParseError::InvalidFieldCount {
            line,
            record: "theory lemma",
            expected: THEORY_RECORD_USAGE,
            found: tokens.len(),
        });
    }

    let id = parse_clause_id(tokens[1], line)?;
    record_clause_id(seen_clause_ids, id, line)?;
    let theory = tokens[2].to_string();
    let literals = parse_clause_literals(&tokens[3..], line)?;

    Ok(TheoryLemma {
        id,
        theory,
        clause: Clause { id, literals },
    })
}

pub(crate) fn parse_resolution_step(
    raw_line: &str,
    line: usize,
    seen_clause_ids: &mut BTreeMap<ClauseId, usize>,
) -> Result<ResolutionStep, ParseError> {
    let tokens: Vec<&str> = raw_line.split_ascii_whitespace().collect();
    if tokens.len() < 5 {
        return Err(ParseError::InvalidFieldCount {
            line,
            record: "resolution",
            expected: RESOLUTION_RECORD_USAGE,
            found: tokens.len(),
        });
    }

    let id = parse_clause_id(tokens[1], line)?;
    record_clause_id(seen_clause_ids, id, line)?;
    let pivot = parse_literal_id(tokens[2], line)?;
    if pivot == 0 {
        return Err(ParseError::ZeroPivot { line });
    }

    Ok(ResolutionStep {
        id,
        pivot,
        parent1: parse_clause_id(tokens[3], line)?,
        parent2: parse_clause_id(tokens[4], line)?,
        result_literals: if tokens.len() == 5 {
            None
        } else {
            Some(parse_clause_literals(&tokens[5..], line)?)
        },
    })
}

pub(crate) fn parse_clause_id(token: &str, line: usize) -> Result<ClauseId, ParseError> {
    token.parse().map_err(|_| ParseError::InvalidClauseId {
        line,
        value: token.to_string(),
    })
}

pub(crate) fn parse_literal_id(token: &str, line: usize) -> Result<LiteralId, ParseError> {
    token.parse().map_err(|_| ParseError::InvalidLiteral {
        line,
        value: token.to_string(),
    })
}

pub(crate) fn parse_clause_literals(
    tokens: &[&str],
    line: usize,
) -> Result<Vec<LiteralId>, ParseError> {
    let Some(terminator_index) = tokens.iter().position(|token| *token == "0") else {
        return Err(ParseError::MissingClauseTerminator { line });
    };

    if terminator_index != tokens.len() - 1 {
        return Err(ParseError::ClauseTerminatorNotLast { line });
    }

    let mut literals = Vec::with_capacity(tokens.len().saturating_sub(1));
    for token in &tokens[..terminator_index] {
        let literal = parse_literal_id(token, line)?;
        if literal == 0 {
            return Err(ParseError::ZeroLiteral {
                line,
                value: (*token).to_string(),
            });
        }
        literals.push(literal);
    }

    Ok(literals)
}

pub(crate) fn record_clause_id(
    seen_clause_ids: &mut BTreeMap<ClauseId, usize>,
    id: ClauseId,
    line: usize,
) -> Result<(), ParseError> {
    if let Some(previous_line) = seen_clause_ids.get(&id) {
        return Err(ParseError::DuplicateClauseId {
            line,
            previous_line: *previous_line,
            id,
        });
    }

    seen_clause_ids.insert(id, line);
    Ok(())
}

pub(crate) fn append_clause_record(
    out: &mut String,
    prefix: &str,
    id: ClauseId,
    theory: Option<&str>,
    literals: &[LiteralId],
) {
    out.push_str(prefix);
    out.push(' ');
    out.push_str(&id.to_string());

    if let Some(theory_name) = theory {
        out.push(' ');
        out.push_str(theory_name);
    }

    for literal in literals {
        out.push(' ');
        out.push_str(&literal.to_string());
    }

    out.push_str(" 0\n");
}

#[cfg(test)]
mod tests {
    use super::{format_proof_trace, parse_proof_trace, ParseError};
    use crate::types::{Clause, ProofTrace, ResolutionStep, TheoryLemma};

    fn clause(id: u64, literals: &[i64]) -> Clause {
        Clause {
            id,
            literals: literals.to_vec(),
        }
    }

    fn step(id: u64, pivot: i64, parent1: u64, parent2: u64) -> ResolutionStep {
        ResolutionStep {
            id,
            pivot,
            parent1,
            parent2,
            result_literals: None,
        }
    }

    fn lemma(id: u64, theory: &str, literals: &[i64]) -> TheoryLemma {
        TheoryLemma {
            id,
            theory: theory.to_string(),
            clause: clause(id, literals),
        }
    }

    #[test]
    fn parses_valid_trace() {
        let input = "i 1 1 0\ni 2 -1 0\nr 3 1 1 2\ne 3\n";
        let trace = parse_proof_trace(input).expect("valid trace should parse");

        assert_eq!(
            trace,
            ProofTrace {
                input_clauses: vec![clause(1, &[1]), clause(2, &[-1])],
                resolution_steps: vec![step(3, 1, 1, 2)],
                theory_lemmas: vec![],
                empty_clause_id: 3,
            }
        );
    }

    #[test]
    fn parses_theory_lemma() {
        let input = "i 1 1 0\nt 2 EUF -1 0\nr 3 1 1 2\ne 3\n";
        let trace = parse_proof_trace(input).expect("theory lemma should parse");

        assert_eq!(
            trace,
            ProofTrace {
                input_clauses: vec![clause(1, &[1])],
                resolution_steps: vec![step(3, 1, 1, 2)],
                theory_lemmas: vec![lemma(2, "EUF", &[-1])],
                empty_clause_id: 3,
            }
        );
    }

    #[test]
    fn round_trips_trace() {
        let trace = ProofTrace {
            input_clauses: vec![clause(1, &[1, 2]), clause(2, &[-1])],
            resolution_steps: vec![
                ResolutionStep {
                    id: 4,
                    pivot: 1,
                    parent1: 1,
                    parent2: 2,
                    result_literals: Some(vec![2]),
                },
                ResolutionStep {
                    id: 5,
                    pivot: 2,
                    parent1: 4,
                    parent2: 3,
                    result_literals: Some(vec![]),
                },
            ],
            theory_lemmas: vec![lemma(3, "LRA", &[-2])],
            empty_clause_id: 5,
        };

        let formatted = format_proof_trace(&trace);
        let reparsed = parse_proof_trace(&formatted).expect("formatted trace should parse");

        assert_eq!(reparsed, trace);
    }

    #[test]
    fn ignores_comments_and_blank_lines() {
        let input = "c input clause follows\n\ni 1 0\n   \nc empty clause marker follows\ne 1\n";
        let trace = parse_proof_trace(input).expect("comments and blank lines should be ignored");

        assert_eq!(
            trace,
            ProofTrace {
                input_clauses: vec![clause(1, &[])],
                resolution_steps: vec![],
                theory_lemmas: vec![],
                empty_clause_id: 1,
            }
        );
    }

    #[test]
    fn rejects_empty_input() {
        let error = parse_proof_trace("").expect_err("empty input should fail");
        assert_eq!(error, ParseError::MissingEmptyClause);
    }

    #[test]
    fn rejects_unknown_record() {
        let error = parse_proof_trace("x 1 2 3\n").expect_err("unknown record should fail");
        assert_eq!(
            error,
            ParseError::UnrecognizedRecord {
                line: 1,
                content: "x 1 2 3".to_string(),
            }
        );
    }

    #[test]
    fn rejects_missing_clause_terminator() {
        let error = parse_proof_trace("i 1 1\n").expect_err("missing terminator should fail");
        assert_eq!(error, ParseError::MissingClauseTerminator { line: 1 });
    }

    #[test]
    fn rejects_resolution_with_wrong_arity() {
        let error = parse_proof_trace("r 3 1 1\ne 3\n")
            .expect_err("malformed resolution record should fail");
        assert_eq!(
            error,
            ParseError::InvalidFieldCount {
                line: 1,
                record: "resolution",
                expected: "r <result_id> <pivot> <parent1> <parent2> [<lit1> <lit2> ... 0]",
                found: 4,
            }
        );
    }

    #[test]
    fn parses_resolution_result_clause() {
        let input = "i 1 1 2 0\ni 2 -1 0\nr 3 1 1 2 2 0\ne 3\n";
        let trace = parse_proof_trace(input).expect("resolution result should parse");

        assert_eq!(
            trace.resolution_steps,
            vec![ResolutionStep {
                id: 3,
                pivot: 1,
                parent1: 1,
                parent2: 2,
                result_literals: Some(vec![2]),
            }]
        );
    }

    #[test]
    fn rejects_resolution_result_without_terminator() {
        let error = parse_proof_trace("i 1 1 0\ni 2 -1 0\nr 3 1 1 2 2\ne 3\n")
            .expect_err("missing resolution result terminator should fail");
        assert_eq!(error, ParseError::MissingClauseTerminator { line: 3 });
    }

    #[test]
    fn rejects_missing_empty_clause_marker() {
        let error =
            parse_proof_trace("i 1 1 0\n").expect_err("missing empty clause marker should fail");
        assert_eq!(error, ParseError::MissingEmptyClause);
    }

    #[test]
    fn rejects_duplicate_clause_ids() {
        let error =
            parse_proof_trace("i 1 1 0\nr 1 1 1 1\ne 1\n").expect_err("duplicate ids should fail");
        assert_eq!(
            error,
            ParseError::DuplicateClauseId {
                line: 2,
                previous_line: 1,
                id: 1,
            }
        );
    }

    #[test]
    fn rejects_duplicate_empty_clause_marker() {
        let error = parse_proof_trace("i 1 0\ne 1\ne 1\n")
            .expect_err("duplicate empty clause markers should fail");
        assert_eq!(
            error,
            ParseError::DuplicateEmptyClause {
                line: 3,
                previous_line: 2,
            }
        );
    }

    #[test]
    fn rejects_unknown_empty_clause_id() {
        let error =
            parse_proof_trace("i 1 0\ne 2\n").expect_err("unknown empty clause id should fail");
        assert_eq!(error, ParseError::UnknownEmptyClauseId { line: 2, id: 2 });
    }

    #[test]
    fn rejects_zero_pivot() {
        let error = parse_proof_trace("i 1 1 0\ni 2 -1 0\nr 3 0 1 2\ne 3\n")
            .expect_err("zero pivot should fail");
        assert_eq!(error, ParseError::ZeroPivot { line: 3 });
    }

    #[test]
    fn rejects_terminator_before_end_of_line() {
        let error =
            parse_proof_trace("i 1 1 0 2\ne 1\n").expect_err("non-final terminator should fail");
        assert_eq!(error, ParseError::ClauseTerminatorNotLast { line: 1 });
    }

    #[test]
    fn rejects_invalid_theory_lemma_literal() {
        let error =
            parse_proof_trace("t 2 EUF foo 0\ne 2\n").expect_err("invalid literal should fail");
        assert_eq!(
            error,
            ParseError::InvalidLiteral {
                line: 1,
                value: "foo".to_string(),
            }
        );
    }
}
