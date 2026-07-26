// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Multi-format export for proof certificates.
//!
//! Supports four output formats:
//!
//! - **JSON**: Pretty-printed via `serde_json` (human-editable, interoperable).
//! - **Binary**: Compact length-prefixed encoding with varint IDs (~10x smaller
//!   than JSON for large proofs).
//! - **HumanReadable**: Indented proof-tree rendering showing derivation depth.
//! - **SmtLib2**: SMT-LIB 2 compatible proof commands for external checkers.

use std::collections::HashMap;
use std::fmt::Write as FmtWrite;

use thiserror::Error;

use crate::format::{
    Literal, TheoryLemmaKind, TrustVcProofCertificate, WireClause, WireClauseId,
    WireResolutionStep, WireTheoryLemma,
};

// ---------------------------------------------------------------------------
// Export format enum
// ---------------------------------------------------------------------------

/// Selects the serialization format for certificate export.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ExportFormat {
    /// Pretty-printed JSON via `serde_json`.
    Json,
    /// Compact binary encoding with length-prefixed fields and varint IDs.
    Binary,
    /// Human-readable proof tree with indentation showing derivation depth.
    HumanReadable,
    /// SMT-LIB 2 format proof commands.
    SmtLib2,
}

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors arising during certificate export.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ExportError {
    /// JSON serialization failed.
    #[error("JSON serialization error: {0}")]
    Json(#[from] serde_json::Error),

    /// Binary encoding or decoding error.
    #[error("binary codec error: {0}")]
    BinaryCodec(String),

    /// The certificate has an unsupported wire format version.
    #[error("unsupported certificate version {0}")]
    UnsupportedVersion(u32),

    /// Internal formatting error.
    #[error("formatting error: {0}")]
    Fmt(#[from] std::fmt::Error),
}

// ---------------------------------------------------------------------------
// Top-level export entry point
// ---------------------------------------------------------------------------

/// Export a certificate in the specified format.
///
/// Returns the serialized bytes. For text formats (JSON, HumanReadable,
/// SmtLib2) the bytes are valid UTF-8.
#[must_use = "exported bytes should be consumed"]
pub fn export_certificate(
    cert: &TrustVcProofCertificate,
    format: ExportFormat,
) -> Result<Vec<u8>, ExportError> {
    match format {
        ExportFormat::Json => {
            let json = serde_json::to_string_pretty(cert)?;
            Ok(json.into_bytes())
        }
        ExportFormat::Binary => BinaryCodec::encode(cert),
        ExportFormat::HumanReadable => {
            let text = ProofTreeRenderer::render(cert)?;
            Ok(text.into_bytes())
        }
        ExportFormat::SmtLib2 => {
            let text = SmtLib2Renderer::render(cert)?;
            Ok(text.into_bytes())
        }
    }
}

// ---------------------------------------------------------------------------
// ProofTreeRenderer — human-readable proof tree
// ---------------------------------------------------------------------------

/// Renders a proof certificate as an indented tree showing derivation depth.
///
/// Resolution steps are internal nodes. Assumptions (input clauses) and theory
/// lemmas are leaves. Theory lemmas are annotated with `[T:kind]`.
pub(crate) struct ProofTreeRenderer;

impl ProofTreeRenderer {
    /// Render the full certificate as a human-readable string.
    pub(crate) fn render(cert: &TrustVcProofCertificate) -> Result<String, ExportError> {
        let mut out = String::new();

        writeln!(out, "TrustVc Proof Certificate v{}", cert.version)?;
        writeln!(out, "Source hash: {}", hex_encode(&cert.source_hash))?;
        writeln!(out, "VC hash:     {}", hex_encode(&cert.vc_hash))?;
        writeln!(
            out,
            "Metadata:    trust_vc={}, solver={}, timestamp={}",
            cert.metadata.trust_vc_version, cert.metadata.solver_version, cert.metadata.timestamp
        )?;
        writeln!(out)?;

        // Build lookup maps.
        let input_map: HashMap<u64, &WireClause> =
            cert.input_clauses.iter().map(|c| (c.id.0, c)).collect();

        let theory_map: HashMap<u64, &WireTheoryLemma> =
            cert.theory_lemmas.iter().map(|tl| (tl.id.0, tl)).collect();

        let step_map: HashMap<u64, &WireResolutionStep> = cert
            .resolution_steps
            .iter()
            .map(|s| (s.result_id.0, s))
            .collect();

        writeln!(
            out,
            "Proof Tree (root = empty clause #{}):",
            cert.empty_clause_id.0
        )?;
        writeln!(out, "{}", "=".repeat(60))?;

        Self::render_node(
            &mut out,
            cert.empty_clause_id.0,
            0,
            &input_map,
            &theory_map,
            &step_map,
            &mut std::collections::HashSet::new(),
        )?;

        Ok(out)
    }

    /// Recursively render a single node in the proof tree.
    fn render_node(
        out: &mut String,
        clause_id: u64,
        depth: usize,
        input_map: &HashMap<u64, &WireClause>,
        theory_map: &HashMap<u64, &WireTheoryLemma>,
        step_map: &HashMap<u64, &WireResolutionStep>,
        visited: &mut std::collections::HashSet<u64>,
    ) -> Result<(), ExportError> {
        let indent = "  ".repeat(depth);

        // Guard against DAG sharing: if already rendered, show back-reference.
        if !visited.insert(clause_id) {
            writeln!(out, "{indent}(ref #{clause_id})")?;
            return Ok(());
        }

        if let Some(step) = step_map.get(&clause_id) {
            writeln!(
                out,
                "{indent}[resolve] #{} = resolve(#{}, #{}) on pivot {}  -> [{}]",
                clause_id,
                step.antecedent_a.0,
                step.antecedent_b.0,
                step.pivot.0,
                format_literals(&step.result_literals),
            )?;
            Self::render_node(
                out,
                step.antecedent_a.0,
                depth + 1,
                input_map,
                theory_map,
                step_map,
                visited,
            )?;
            Self::render_node(
                out,
                step.antecedent_b.0,
                depth + 1,
                input_map,
                theory_map,
                step_map,
                visited,
            )?;
        } else if let Some(tl) = theory_map.get(&clause_id) {
            let kind_tag = theory_kind_tag(tl.kind);
            let justification = tl
                .justification
                .as_deref()
                .map(|j| format!(" ({j})"))
                .unwrap_or_default();
            writeln!(
                out,
                "{indent}[T:{kind_tag}] #{clause_id} = [{}]{justification}",
                format_literals(&tl.literals),
            )?;
        } else if let Some(clause) = input_map.get(&clause_id) {
            writeln!(
                out,
                "{indent}[assume] #{clause_id} = [{}]",
                format_literals(&clause.literals),
            )?;
        } else {
            writeln!(out, "{indent}[unknown] #{clause_id}")?;
        }

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// BinaryCodec — compact binary encoding
// ---------------------------------------------------------------------------

/// Magic bytes identifying a trust_vc binary proof certificate.
const BINARY_MAGIC: &[u8; 4] = b"CPRF";

/// Current binary format version.
const BINARY_VERSION: u8 = 1;

/// Section tags for the binary format.
const SECTION_INPUT_CLAUSES: u8 = 0x01;
const SECTION_THEORY_LEMMAS: u8 = 0x02;
const SECTION_RESOLUTION_STEPS: u8 = 0x03;
const SECTION_METADATA: u8 = 0x04;
const SECTION_END: u8 = 0xFF;

/// Compact binary encoder/decoder for proof certificates.
///
/// Wire format:
/// ```text
/// [magic: 4 bytes "CPRF"]
/// [binary_version: 1 byte]
/// [cert_version: varint]
/// [source_hash: 32 bytes]
/// [vc_hash: 32 bytes]
/// [empty_clause_id: varint]
/// [sections...]
/// [SECTION_END: 1 byte]
/// ```
///
/// Each section:
/// ```text
/// [section_tag: 1 byte]
/// [count: varint]
/// [items...]
/// ```
pub struct BinaryCodec;

impl BinaryCodec {
    /// Encode a certificate to compact binary.
    #[must_use = "encoded bytes should be consumed"]
    pub fn encode(cert: &TrustVcProofCertificate) -> Result<Vec<u8>, ExportError> {
        let mut buf = Vec::new();

        // Header
        buf.extend_from_slice(BINARY_MAGIC);
        buf.push(BINARY_VERSION);
        encode_varint(&mut buf, cert.version as u64);
        buf.extend_from_slice(&cert.source_hash);
        buf.extend_from_slice(&cert.vc_hash);
        encode_varint(&mut buf, cert.empty_clause_id.0);

        // Section: input clauses
        buf.push(SECTION_INPUT_CLAUSES);
        encode_varint(&mut buf, cert.input_clauses.len() as u64);
        for clause in &cert.input_clauses {
            Self::encode_clause(&mut buf, clause);
        }

        // Section: theory lemmas
        buf.push(SECTION_THEORY_LEMMAS);
        encode_varint(&mut buf, cert.theory_lemmas.len() as u64);
        for lemma in &cert.theory_lemmas {
            Self::encode_theory_lemma(&mut buf, lemma);
        }

        // Section: resolution steps
        buf.push(SECTION_RESOLUTION_STEPS);
        encode_varint(&mut buf, cert.resolution_steps.len() as u64);
        for step in &cert.resolution_steps {
            Self::encode_resolution_step(&mut buf, step);
        }

        // Section: metadata
        buf.push(SECTION_METADATA);
        Self::encode_string(&mut buf, &cert.metadata.timestamp);
        Self::encode_string(&mut buf, &cert.metadata.trust_vc_version);
        Self::encode_string(&mut buf, &cert.metadata.solver_version);

        // Terminator
        buf.push(SECTION_END);

        Ok(buf)
    }

    /// Decode a certificate from compact binary.
    #[must_use = "decoded certificate should be used"]
    pub fn decode(data: &[u8]) -> Result<TrustVcProofCertificate, ExportError> {
        // Header
        if data.len() < 5 {
            return Err(ExportError::BinaryCodec(
                "data too short for header".to_string(),
            ));
        }
        if &data[0..4] != BINARY_MAGIC {
            return Err(ExportError::BinaryCodec("invalid magic bytes".to_string()));
        }
        let mut pos = 4;

        let binary_version = data[pos];
        pos += 1;
        if binary_version != BINARY_VERSION {
            return Err(ExportError::BinaryCodec(format!(
                "unsupported binary version {binary_version}, expected {BINARY_VERSION}"
            )));
        }

        let (cert_version, n) = decode_varint(&data[pos..])?;
        pos += n;

        if pos + 64 > data.len() {
            return Err(ExportError::BinaryCodec(
                "data too short for hashes".to_string(),
            ));
        }
        let mut source_hash = [0u8; 32];
        source_hash.copy_from_slice(&data[pos..pos + 32]);
        pos += 32;

        let mut vc_hash = [0u8; 32];
        vc_hash.copy_from_slice(&data[pos..pos + 32]);
        pos += 32;

        let (empty_clause_id, n) = decode_varint(&data[pos..])?;
        pos += n;

        let mut input_clauses = Vec::new();
        let mut theory_lemmas = Vec::new();
        let mut resolution_steps = Vec::new();
        let mut metadata_timestamp = String::new();
        let mut metadata_trust_vc_version = String::new();
        let mut metadata_solver_version = String::new();

        // Read sections until end marker.
        loop {
            if pos >= data.len() {
                return Err(ExportError::BinaryCodec(
                    "unexpected end of data".to_string(),
                ));
            }

            let tag = data[pos];
            pos += 1;

            if tag == SECTION_END {
                break;
            }

            match tag {
                SECTION_INPUT_CLAUSES => {
                    let (count, n) = decode_varint(&data[pos..])?;
                    pos += n;
                    for _ in 0..count {
                        let (clause, n) = Self::decode_clause(&data[pos..])?;
                        pos += n;
                        input_clauses.push(clause);
                    }
                }
                SECTION_THEORY_LEMMAS => {
                    let (count, n) = decode_varint(&data[pos..])?;
                    pos += n;
                    for _ in 0..count {
                        let (lemma, n) = Self::decode_theory_lemma(&data[pos..])?;
                        pos += n;
                        theory_lemmas.push(lemma);
                    }
                }
                SECTION_RESOLUTION_STEPS => {
                    let (count, n) = decode_varint(&data[pos..])?;
                    pos += n;
                    for _ in 0..count {
                        let (step, n) = Self::decode_resolution_step(&data[pos..])?;
                        pos += n;
                        resolution_steps.push(step);
                    }
                }
                SECTION_METADATA => {
                    let (ts, n) = Self::decode_string(&data[pos..])?;
                    pos += n;
                    metadata_timestamp = ts;
                    let (cv, n) = Self::decode_string(&data[pos..])?;
                    pos += n;
                    metadata_trust_vc_version = cv;
                    let (sv, n) = Self::decode_string(&data[pos..])?;
                    pos += n;
                    metadata_solver_version = sv;
                }
                other => {
                    return Err(ExportError::BinaryCodec(format!(
                        "unknown section tag 0x{other:02x}"
                    )));
                }
            }
        }

        Ok(TrustVcProofCertificate {
            version: u32::try_from(cert_version).map_err(|_| {
                ExportError::BinaryCodec(format!(
                    "certificate version {} exceeds u32::MAX",
                    cert_version
                ))
            })?,
            source_hash,
            vc_hash,
            resolution_steps,
            theory_lemmas,
            input_clauses,
            empty_clause_id: WireClauseId(empty_clause_id),
            metadata: crate::format::CertificateMetadata {
                timestamp: metadata_timestamp,
                trust_vc_version: metadata_trust_vc_version,
                solver_version: metadata_solver_version,
            },
        })
    }

    // -- Clause encoding --

    fn encode_clause(buf: &mut Vec<u8>, clause: &WireClause) {
        encode_varint(buf, clause.id.0);
        encode_varint(buf, clause.literals.len() as u64);
        for lit in &clause.literals {
            encode_signed(buf, lit.0);
        }
    }

    fn decode_clause(data: &[u8]) -> Result<(WireClause, usize), ExportError> {
        let mut pos = 0;
        let (id, n) = decode_varint(&data[pos..])?;
        pos += n;
        let (lit_count, n) = decode_varint(&data[pos..])?;
        pos += n;
        // Cap capacity hint at remaining data length to avoid allocator abuse from corrupt data.
        let cap = usize::try_from(lit_count)
            .unwrap_or(usize::MAX)
            .min(data.len().saturating_sub(pos));
        let mut literals = Vec::with_capacity(cap);
        for _ in 0..lit_count {
            let (lit, n) = decode_signed(&data[pos..])?;
            pos += n;
            literals.push(Literal(lit));
        }
        Ok((
            WireClause {
                id: WireClauseId(id),
                literals,
            },
            pos,
        ))
    }

    // -- Theory lemma encoding --

    fn encode_theory_lemma(buf: &mut Vec<u8>, lemma: &WireTheoryLemma) {
        encode_varint(buf, lemma.id.0);
        buf.push(theory_kind_to_byte(lemma.kind));
        encode_varint(buf, lemma.literals.len() as u64);
        for lit in &lemma.literals {
            encode_signed(buf, lit.0);
        }
        // Justification: length-prefixed string (0 = none).
        match &lemma.justification {
            Some(j) => Self::encode_string(buf, j),
            None => encode_varint(buf, 0),
        }
    }

    fn decode_theory_lemma(data: &[u8]) -> Result<(WireTheoryLemma, usize), ExportError> {
        let mut pos = 0;
        let (id, n) = decode_varint(&data[pos..])?;
        pos += n;

        if pos >= data.len() {
            return Err(ExportError::BinaryCodec(
                "unexpected end reading theory kind".to_string(),
            ));
        }
        let kind = theory_kind_from_byte(data[pos])?;
        pos += 1;

        let (lit_count, n) = decode_varint(&data[pos..])?;
        pos += n;
        // Cap capacity hint at remaining data length to avoid allocator abuse from corrupt data.
        let cap = usize::try_from(lit_count)
            .unwrap_or(usize::MAX)
            .min(data.len().saturating_sub(pos));
        let mut literals = Vec::with_capacity(cap);
        for _ in 0..lit_count {
            let (lit, n) = decode_signed(&data[pos..])?;
            pos += n;
            literals.push(Literal(lit));
        }

        let (justification_str, n) = Self::decode_string(&data[pos..])?;
        pos += n;
        let justification = if justification_str.is_empty() {
            None
        } else {
            Some(justification_str)
        };

        Ok((
            WireTheoryLemma {
                id: WireClauseId(id),
                kind,
                literals,
                justification,
            },
            pos,
        ))
    }

    // -- Resolution step encoding --

    fn encode_resolution_step(buf: &mut Vec<u8>, step: &WireResolutionStep) {
        encode_varint(buf, step.result_id.0);
        encode_varint(buf, step.antecedent_a.0);
        encode_varint(buf, step.antecedent_b.0);
        encode_signed(buf, step.pivot.0);
        encode_varint(buf, step.result_literals.len() as u64);
        for lit in &step.result_literals {
            encode_signed(buf, lit.0);
        }
    }

    fn decode_resolution_step(data: &[u8]) -> Result<(WireResolutionStep, usize), ExportError> {
        let mut pos = 0;
        let (result_id, n) = decode_varint(&data[pos..])?;
        pos += n;
        let (antecedent_a, n) = decode_varint(&data[pos..])?;
        pos += n;
        let (antecedent_b, n) = decode_varint(&data[pos..])?;
        pos += n;
        let (pivot, n) = decode_signed(&data[pos..])?;
        pos += n;
        let (lit_count, n) = decode_varint(&data[pos..])?;
        pos += n;
        // Cap capacity hint at remaining data length to avoid allocator abuse from corrupt data.
        let cap = usize::try_from(lit_count)
            .unwrap_or(usize::MAX)
            .min(data.len().saturating_sub(pos));
        let mut result_literals = Vec::with_capacity(cap);
        for _ in 0..lit_count {
            let (lit, n) = decode_signed(&data[pos..])?;
            pos += n;
            result_literals.push(Literal(lit));
        }
        Ok((
            WireResolutionStep {
                result_id: WireClauseId(result_id),
                antecedent_a: WireClauseId(antecedent_a),
                antecedent_b: WireClauseId(antecedent_b),
                pivot: Literal(pivot),
                result_literals,
            },
            pos,
        ))
    }

    // -- String encoding --

    fn encode_string(buf: &mut Vec<u8>, s: &str) {
        encode_varint(buf, s.len() as u64);
        buf.extend_from_slice(s.as_bytes());
    }

    fn decode_string(data: &[u8]) -> Result<(String, usize), ExportError> {
        let (len, n) = decode_varint(data)?;
        let total = n + len as usize;
        if data.len() < total {
            return Err(ExportError::BinaryCodec(
                "unexpected end reading string".to_string(),
            ));
        }
        let s = std::str::from_utf8(&data[n..total])
            .map_err(|e| ExportError::BinaryCodec(format!("invalid UTF-8: {e}")))?
            .to_string();
        Ok((s, total))
    }
}

// ---------------------------------------------------------------------------
// SmtLib2Renderer — SMT-LIB 2 proof commands
// ---------------------------------------------------------------------------

/// Renders a proof certificate as SMT-LIB 2 proof commands.
///
/// Output format:
/// - `(assert ...)` for input clause assumptions
/// - `(theory-lemma ...)` for theory lemmas with kind annotation
/// - `(step ...)` for resolution steps with pivot and antecedent info
/// - `(qed ...)` for the final empty clause
pub(crate) struct SmtLib2Renderer;

impl SmtLib2Renderer {
    /// Render the certificate as an SMT-LIB 2 compatible proof script.
    pub(crate) fn render(cert: &TrustVcProofCertificate) -> Result<String, ExportError> {
        let mut out = String::new();

        writeln!(out, "; TrustVc Proof Certificate v{}", cert.version)?;
        writeln!(out, "; Source hash: {}", hex_encode(&cert.source_hash))?;
        writeln!(out, "; VC hash:     {}", hex_encode(&cert.vc_hash))?;
        writeln!(out)?;

        // Input clauses as assertions.
        for clause in &cert.input_clauses {
            write!(out, "(assert (! ")?;
            Self::write_clause_expr(&mut out, &clause.literals)?;
            writeln!(out, " :named c{}))", clause.id.0)?;
        }

        if !cert.input_clauses.is_empty() {
            writeln!(out)?;
        }

        // Theory lemmas.
        for lemma in &cert.theory_lemmas {
            let kind_tag = theory_kind_tag(lemma.kind);
            write!(out, "(theory-lemma (! ")?;
            Self::write_clause_expr(&mut out, &lemma.literals)?;
            write!(out, " :named c{} :theory {kind_tag}", lemma.id.0)?;
            if let Some(ref j) = lemma.justification {
                write!(out, " :justification \"{j}\"")?;
            }
            writeln!(out, "))")?;
        }

        if !cert.theory_lemmas.is_empty() {
            writeln!(out)?;
        }

        // Resolution steps.
        for step in &cert.resolution_steps {
            write!(out, "(step c{} (cl", step.result_id.0,)?;
            for lit in &step.result_literals {
                write!(out, " {}", Self::literal_to_smtlib(lit))?;
            }
            write!(
                out,
                ") :rule resolution :premises (c{} c{})",
                step.antecedent_a.0, step.antecedent_b.0,
            )?;
            writeln!(out, " :pivot {})", Self::literal_to_smtlib(&step.pivot))?;
        }

        if !cert.resolution_steps.is_empty() {
            writeln!(out)?;
        }

        // Final empty clause.
        writeln!(out, "(qed c{})", cert.empty_clause_id.0)?;

        Ok(out)
    }

    /// Write a clause expression as an SMT-LIB 2 `(or ...)` or single literal.
    fn write_clause_expr(out: &mut String, literals: &[Literal]) -> Result<(), ExportError> {
        match literals.len() {
            0 => write!(out, "false")?,
            1 => write!(out, "{}", Self::literal_to_smtlib(&literals[0]))?,
            _ => {
                write!(out, "(or")?;
                for lit in literals {
                    write!(out, " {}", Self::literal_to_smtlib(lit))?;
                }
                write!(out, ")")?;
            }
        }
        Ok(())
    }

    /// Convert a literal to its SMT-LIB 2 representation.
    fn literal_to_smtlib(lit: &Literal) -> String {
        if lit.0 >= 0 {
            format!("v{}", lit.0)
        } else {
            format!("(not v{})", -lit.0)
        }
    }
}

// ---------------------------------------------------------------------------
// Varint encoding (LEB128 unsigned)
// ---------------------------------------------------------------------------

/// Encode a `u64` as a variable-length integer (LEB128).
fn encode_varint(buf: &mut Vec<u8>, mut value: u64) {
    loop {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Decode a LEB128 varint from a byte slice. Returns `(value, bytes_consumed)`.
fn decode_varint(data: &[u8]) -> Result<(u64, usize), ExportError> {
    let mut value: u64 = 0;
    let mut shift = 0u32;
    for (i, &byte) in data.iter().enumerate() {
        if shift >= 64 {
            return Err(ExportError::BinaryCodec("varint overflow".to_string()));
        }
        value |= ((byte & 0x7F) as u64) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return Ok((value, i + 1));
        }
    }
    Err(ExportError::BinaryCodec("unterminated varint".to_string()))
}

/// Encode a signed `i64` using zigzag encoding then varint.
fn encode_signed(buf: &mut Vec<u8>, value: i64) {
    let zigzag = ((value << 1) ^ (value >> 63)) as u64;
    encode_varint(buf, zigzag);
}

/// Decode a zigzag-encoded signed varint. Returns `(value, bytes_consumed)`.
fn decode_signed(data: &[u8]) -> Result<(i64, usize), ExportError> {
    let (zigzag, n) = decode_varint(data)?;
    let value = ((zigzag >> 1) as i64) ^ -((zigzag & 1) as i64);
    Ok((value, n))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

use crate::hex_encode;

/// Format a slice of literals as a comma-separated string.
fn format_literals(literals: &[Literal]) -> String {
    literals
        .iter()
        .map(|l| l.0.to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Convert a `TheoryLemmaKind` to a short human-readable tag.
fn theory_kind_tag(kind: TheoryLemmaKind) -> &'static str {
    match kind {
        TheoryLemmaKind::Euf => "EUF",
        TheoryLemmaKind::Lra => "LRA",
        TheoryLemmaKind::Nia => "NIA",
        TheoryLemmaKind::BitVector => "BV",
        TheoryLemmaKind::Array => "Array",
        TheoryLemmaKind::Sequence => "Seq",
        TheoryLemmaKind::Other => "Other",
    }
}

/// Encode a `TheoryLemmaKind` as a single byte for binary format.
fn theory_kind_to_byte(kind: TheoryLemmaKind) -> u8 {
    match kind {
        TheoryLemmaKind::Euf => 0,
        TheoryLemmaKind::Lra => 1,
        TheoryLemmaKind::Nia => 2,
        TheoryLemmaKind::BitVector => 3,
        TheoryLemmaKind::Array => 4,
        TheoryLemmaKind::Sequence => 5,
        TheoryLemmaKind::Other => 6,
    }
}

/// Decode a `TheoryLemmaKind` from a single byte.
fn theory_kind_from_byte(b: u8) -> Result<TheoryLemmaKind, ExportError> {
    match b {
        0 => Ok(TheoryLemmaKind::Euf),
        1 => Ok(TheoryLemmaKind::Lra),
        2 => Ok(TheoryLemmaKind::Nia),
        3 => Ok(TheoryLemmaKind::BitVector),
        4 => Ok(TheoryLemmaKind::Array),
        5 => Ok(TheoryLemmaKind::Sequence),
        6 => Ok(TheoryLemmaKind::Other),
        other => Err(ExportError::BinaryCodec(format!(
            "unknown theory kind byte 0x{other:02x}"
        ))),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::format::{
        CertificateMetadata, Literal, TheoryLemmaKind, TrustVcProofCertificate, WireClause,
        WireClauseId, WireResolutionStep, WireTheoryLemma, CERTIFICATE_VERSION,
    };

    /// Build a minimal valid certificate for testing.
    fn minimal_certificate() -> TrustVcProofCertificate {
        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: crate::format::sha256(b"fn main() {}"),
            vc_hash: crate::format::sha256(b"(assert (not true))"),
            resolution_steps: vec![],
            theory_lemmas: vec![],
            input_clauses: vec![WireClause {
                id: WireClauseId(0),
                literals: vec![],
            }],
            empty_clause_id: WireClauseId(0),
            metadata: CertificateMetadata {
                timestamp: "2026-03-28T00:00:00Z".to_string(),
                trust_vc_version: "1.0.0".to_string(),
                solver_version: "ay-dpll 0.1.0".to_string(),
            },
        }
    }

    /// Build a certificate with resolution steps and theory lemmas.
    fn rich_certificate() -> TrustVcProofCertificate {
        // Proof tree:
        //   #6 = resolve(#4, #5) on pivot 2  -> []   (empty clause)
        //   #4 = resolve(#1, #2) on pivot 1  -> [2]
        //   #5 = resolve(#3, #10) on pivot 3 -> [-2]
        //   #1 = [1, 2]  (input)
        //   #2 = [-1]    (input)
        //   #3 = [-2, 3] (input)
        //   #10 = [3, -4] (EUF theory lemma) — referenced by step #5
        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: crate::format::sha256(b"fn verified()"),
            vc_hash: crate::format::sha256(b"(vc)"),
            input_clauses: vec![
                WireClause {
                    id: WireClauseId(1),
                    literals: vec![Literal(1), Literal(2)],
                },
                WireClause {
                    id: WireClauseId(2),
                    literals: vec![Literal(-1)],
                },
                WireClause {
                    id: WireClauseId(3),
                    literals: vec![Literal(-2), Literal(3)],
                },
            ],
            theory_lemmas: vec![WireTheoryLemma {
                id: WireClauseId(10),
                kind: TheoryLemmaKind::Euf,
                literals: vec![Literal(-3)],
                justification: Some("congruence closure".to_string()),
            }],
            resolution_steps: vec![
                WireResolutionStep {
                    result_id: WireClauseId(4),
                    antecedent_a: WireClauseId(1),
                    antecedent_b: WireClauseId(2),
                    pivot: Literal(1),
                    result_literals: vec![Literal(2)],
                },
                WireResolutionStep {
                    result_id: WireClauseId(5),
                    antecedent_a: WireClauseId(3),
                    antecedent_b: WireClauseId(10),
                    pivot: Literal(3),
                    result_literals: vec![Literal(-2)],
                },
                WireResolutionStep {
                    result_id: WireClauseId(6),
                    antecedent_a: WireClauseId(4),
                    antecedent_b: WireClauseId(5),
                    pivot: Literal(2),
                    result_literals: vec![],
                },
            ],
            empty_clause_id: WireClauseId(6),
            metadata: CertificateMetadata {
                timestamp: "2026-03-28T12:00:00Z".to_string(),
                trust_vc_version: "1.0.0".to_string(),
                solver_version: "ay-dpll 0.1.0".to_string(),
            },
        }
    }

    /// Build a large certificate for compression ratio testing.
    fn large_certificate(num_steps: usize) -> TrustVcProofCertificate {
        let mut input_clauses = vec![WireClause {
            id: WireClauseId(1),
            literals: vec![Literal(1)],
        }];
        for i in 1..=num_steps {
            input_clauses.push(WireClause {
                id: WireClauseId(1 + i as u64),
                literals: vec![Literal(-(i as i64)), Literal(i as i64 + 1)],
            });
        }
        input_clauses.push(WireClause {
            id: WireClauseId(num_steps as u64 + 2),
            literals: vec![Literal(-(num_steps as i64 + 1))],
        });

        let base = 1000u64;
        let mut steps = Vec::with_capacity(num_steps + 1);
        // First step: resolve input 1 with input 2
        steps.push(WireResolutionStep {
            result_id: WireClauseId(base),
            antecedent_a: WireClauseId(1),
            antecedent_b: WireClauseId(2),
            pivot: Literal(1),
            result_literals: vec![Literal(2)],
        });
        for i in 1..num_steps {
            steps.push(WireResolutionStep {
                result_id: WireClauseId(base + i as u64),
                antecedent_a: WireClauseId(base + i as u64 - 1),
                antecedent_b: WireClauseId(i as u64 + 2),
                pivot: Literal(i as i64 + 1),
                result_literals: vec![Literal(i as i64 + 2)],
            });
        }
        // Final step yielding empty clause
        let final_id = base + num_steps as u64;
        steps.push(WireResolutionStep {
            result_id: WireClauseId(final_id),
            antecedent_a: WireClauseId(final_id - 1),
            antecedent_b: WireClauseId(num_steps as u64 + 2),
            pivot: Literal(num_steps as i64 + 1),
            result_literals: vec![],
        });

        TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: crate::format::sha256(b"large proof"),
            vc_hash: crate::format::sha256(b"(vc-large)"),
            input_clauses,
            theory_lemmas: vec![],
            resolution_steps: steps,
            empty_clause_id: WireClauseId(final_id),
            metadata: CertificateMetadata {
                timestamp: "2026-03-28T12:00:00Z".to_string(),
                trust_vc_version: "1.0.0".to_string(),
                solver_version: "ay-dpll 0.1.0".to_string(),
            },
        }
    }

    // -- JSON format tests ----------------------------------------------------

    #[test]
    fn test_export_json_roundtrip_minimal() {
        let cert = minimal_certificate();
        let bytes =
            export_certificate(&cert, ExportFormat::Json).expect("JSON export should succeed");
        let json_str = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        let recovered: TrustVcProofCertificate =
            serde_json::from_str(json_str).expect("JSON deserialization should succeed");
        assert_eq!(cert, recovered);
    }

    #[test]
    fn test_export_json_roundtrip_rich() {
        let cert = rich_certificate();
        let bytes =
            export_certificate(&cert, ExportFormat::Json).expect("JSON export should succeed");
        let json_str = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        let recovered: TrustVcProofCertificate =
            serde_json::from_str(json_str).expect("JSON deserialization should succeed");
        assert_eq!(cert, recovered);
    }

    #[test]
    fn test_export_json_is_pretty_printed() {
        let cert = minimal_certificate();
        let bytes =
            export_certificate(&cert, ExportFormat::Json).expect("JSON export should succeed");
        let json_str = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        // Pretty-printed JSON contains newlines and indentation.
        assert!(json_str.contains('\n'), "should be pretty-printed");
        assert!(json_str.contains("  "), "should have indentation");
    }

    // -- Binary format tests --------------------------------------------------

    #[test]
    fn test_export_binary_roundtrip_minimal() {
        let cert = minimal_certificate();
        let bytes = BinaryCodec::encode(&cert).expect("binary encode should succeed");
        let recovered = BinaryCodec::decode(&bytes).expect("binary decode should succeed");
        assert_eq!(cert, recovered);
    }

    #[test]
    fn test_export_binary_roundtrip_rich() {
        let cert = rich_certificate();
        let bytes = BinaryCodec::encode(&cert).expect("binary encode should succeed");
        let recovered = BinaryCodec::decode(&bytes).expect("binary decode should succeed");
        assert_eq!(cert, recovered);
    }

    #[test]
    fn test_export_binary_magic_header() {
        let cert = minimal_certificate();
        let bytes = BinaryCodec::encode(&cert).expect("binary encode should succeed");
        assert_eq!(&bytes[0..4], b"CPRF", "should start with magic bytes");
        assert_eq!(bytes[4], BINARY_VERSION, "binary version byte");
    }

    #[test]
    fn test_export_binary_rejects_invalid_magic() {
        let err = BinaryCodec::decode(b"JUNK\x01").expect_err("should reject invalid magic");
        match err {
            ExportError::BinaryCodec(msg) => assert!(msg.contains("magic")),
            other => panic!("expected BinaryCodec error, got: {other:?}"),
        }
    }

    #[test]
    fn test_export_binary_rejects_short_data() {
        let err = BinaryCodec::decode(b"CP").expect_err("should reject short data");
        match err {
            ExportError::BinaryCodec(msg) => assert!(msg.contains("too short")),
            other => panic!("expected BinaryCodec error, got: {other:?}"),
        }
    }

    #[test]
    fn test_export_binary_smaller_than_json() {
        let cert = large_certificate(100);
        let json_bytes =
            export_certificate(&cert, ExportFormat::Json).expect("JSON export should succeed");
        let binary_bytes =
            export_certificate(&cert, ExportFormat::Binary).expect("binary export should succeed");
        // Binary should be significantly smaller than JSON.
        assert!(
            binary_bytes.len() < json_bytes.len() / 2,
            "binary ({} bytes) should be much smaller than JSON ({} bytes)",
            binary_bytes.len(),
            json_bytes.len(),
        );
    }

    #[test]
    fn test_export_binary_roundtrip_large() {
        let cert = large_certificate(200);
        let bytes = BinaryCodec::encode(&cert).expect("binary encode should succeed");
        let recovered = BinaryCodec::decode(&bytes).expect("binary decode should succeed");
        assert_eq!(
            cert.resolution_steps.len(),
            recovered.resolution_steps.len()
        );
        assert_eq!(cert.input_clauses.len(), recovered.input_clauses.len());
        assert_eq!(cert, recovered);
    }

    #[test]
    fn test_export_binary_all_theory_kinds() {
        let all_kinds = [
            TheoryLemmaKind::Euf,
            TheoryLemmaKind::Lra,
            TheoryLemmaKind::Nia,
            TheoryLemmaKind::BitVector,
            TheoryLemmaKind::Array,
            TheoryLemmaKind::Sequence,
            TheoryLemmaKind::Other,
        ];
        let cert = TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
            input_clauses: vec![],
            resolution_steps: vec![],
            theory_lemmas: all_kinds
                .iter()
                .enumerate()
                .map(|(i, &kind)| WireTheoryLemma {
                    id: WireClauseId(i as u64),
                    kind,
                    literals: vec![Literal(i as i64 + 1)],
                    justification: if i % 2 == 0 {
                        Some(format!("reason-{i}"))
                    } else {
                        None
                    },
                })
                .collect(),
            empty_clause_id: WireClauseId(0),
            metadata: CertificateMetadata {
                timestamp: "2026-03-28T00:00:00Z".to_string(),
                trust_vc_version: "1.0.0".to_string(),
                solver_version: "ay-dpll 0.1.0".to_string(),
            },
        };
        let bytes = BinaryCodec::encode(&cert).expect("encode all theory kinds");
        let recovered = BinaryCodec::decode(&bytes).expect("decode all theory kinds");
        assert_eq!(cert.theory_lemmas.len(), recovered.theory_lemmas.len());
        for (orig, recv) in cert
            .theory_lemmas
            .iter()
            .zip(recovered.theory_lemmas.iter())
        {
            assert_eq!(orig.kind, recv.kind);
            assert_eq!(orig.justification, recv.justification);
        }
    }

    // -- Human-readable format tests ------------------------------------------

    #[test]
    fn test_export_human_readable_contains_header() {
        let cert = minimal_certificate();
        let bytes = export_certificate(&cert, ExportFormat::HumanReadable)
            .expect("human readable export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(text.contains("TrustVc Proof Certificate"));
        assert!(text.contains("Source hash:"));
        assert!(text.contains("VC hash:"));
    }

    #[test]
    fn test_export_human_readable_shows_assumptions() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::HumanReadable)
            .expect("human readable export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(text.contains("[assume]"), "should show assumption leaves");
    }

    #[test]
    fn test_export_human_readable_shows_resolution() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::HumanReadable)
            .expect("human readable export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(text.contains("[resolve]"), "should show resolution steps");
        assert!(text.contains("pivot"), "should show pivot literal");
    }

    #[test]
    fn test_export_human_readable_shows_theory_lemmas() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::HumanReadable)
            .expect("human readable export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(text.contains("[T:EUF]"), "should tag theory lemma kind");
    }

    #[test]
    fn test_export_human_readable_indentation_increases_with_depth() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::HumanReadable)
            .expect("human readable export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        // The root resolve step should have less indentation than its children.
        let lines: Vec<&str> = text.lines().collect();
        let resolve_lines: Vec<&str> = lines
            .iter()
            .filter(|l| l.contains("[resolve]") || l.contains("[assume]"))
            .copied()
            .collect();
        assert!(
            resolve_lines.len() >= 2,
            "should have at least 2 proof tree lines"
        );
        // First resolve line should have fewer leading spaces than assumption lines.
        let first_indent = resolve_lines[0].len() - resolve_lines[0].trim_start().len();
        let last_indent =
            resolve_lines.last().unwrap().len() - resolve_lines.last().unwrap().trim_start().len();
        assert!(
            last_indent >= first_indent,
            "deeper nodes should have more indentation"
        );
    }

    // -- SMT-LIB 2 format tests -----------------------------------------------

    #[test]
    fn test_export_smtlib2_contains_assertions() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::SmtLib2)
            .expect("SmtLib2 export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(
            text.contains("(assert"),
            "should contain assertion commands"
        );
    }

    #[test]
    fn test_export_smtlib2_contains_steps() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::SmtLib2)
            .expect("SmtLib2 export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(text.contains("(step"), "should contain step commands");
        assert!(
            text.contains(":rule resolution"),
            "should contain resolution rule"
        );
        assert!(text.contains(":pivot"), "should contain pivot annotation");
        assert!(text.contains(":premises"), "should contain premises");
    }

    #[test]
    fn test_export_smtlib2_contains_qed() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::SmtLib2)
            .expect("SmtLib2 export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(text.contains("(qed"), "should contain qed command");
    }

    #[test]
    fn test_export_smtlib2_theory_lemma_annotation() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::SmtLib2)
            .expect("SmtLib2 export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(
            text.contains("(theory-lemma"),
            "should contain theory-lemma command"
        );
        assert!(text.contains(":theory EUF"), "should annotate theory kind");
    }

    #[test]
    fn test_export_smtlib2_negated_literals() {
        let cert = rich_certificate();
        let bytes = export_certificate(&cert, ExportFormat::SmtLib2)
            .expect("SmtLib2 export should succeed");
        let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
        assert!(
            text.contains("(not v"),
            "negated literals should use (not vN) syntax"
        );
    }

    // -- Varint encoding tests ------------------------------------------------

    #[test]
    fn test_varint_roundtrip_small_values() {
        for v in [0u64, 1, 127, 128, 255, 256, 16383, 16384] {
            let mut buf = Vec::new();
            encode_varint(&mut buf, v);
            let (decoded, n) = decode_varint(&buf).expect("decode should succeed");
            assert_eq!(decoded, v, "roundtrip failed for {v}");
            assert_eq!(n, buf.len(), "consumed bytes should match buffer length");
        }
    }

    #[test]
    fn test_varint_roundtrip_large_values() {
        for v in [u64::MAX, u64::MAX / 2, 1 << 49, 1 << 56] {
            let mut buf = Vec::new();
            encode_varint(&mut buf, v);
            let (decoded, _) = decode_varint(&buf).expect("decode should succeed");
            assert_eq!(decoded, v, "roundtrip failed for {v}");
        }
    }

    #[test]
    fn test_signed_varint_roundtrip() {
        for v in [0i64, 1, -1, 127, -128, i64::MAX, i64::MIN] {
            let mut buf = Vec::new();
            encode_signed(&mut buf, v);
            let (decoded, _) = decode_signed(&buf).expect("decode should succeed");
            assert_eq!(decoded, v, "signed roundtrip failed for {v}");
        }
    }

    // -- Empty certificate edge cases -----------------------------------------

    #[test]
    fn test_export_all_formats_empty_certificate() {
        let cert = TrustVcProofCertificate {
            version: CERTIFICATE_VERSION,
            source_hash: [0u8; 32],
            vc_hash: [0u8; 32],
            input_clauses: vec![],
            resolution_steps: vec![],
            theory_lemmas: vec![],
            empty_clause_id: WireClauseId(0),
            metadata: CertificateMetadata {
                timestamp: String::new(),
                trust_vc_version: String::new(),
                solver_version: String::new(),
            },
        };

        for fmt in [
            ExportFormat::Json,
            ExportFormat::Binary,
            ExportFormat::HumanReadable,
            ExportFormat::SmtLib2,
        ] {
            let result = export_certificate(&cert, fmt);
            assert!(
                result.is_ok(),
                "export should succeed for empty certificate in format {fmt:?}"
            );
        }
    }

    // -- Cross-format consistency ---------------------------------------------

    #[test]
    fn test_export_binary_via_top_level_roundtrips() {
        let cert = rich_certificate();
        let bytes =
            export_certificate(&cert, ExportFormat::Binary).expect("binary export should succeed");
        let recovered = BinaryCodec::decode(&bytes).expect("binary decode should succeed");
        assert_eq!(cert, recovered);
    }

    #[test]
    fn test_export_json_via_top_level_matches_direct() {
        let cert = rich_certificate();
        let via_export =
            export_certificate(&cert, ExportFormat::Json).expect("JSON export should succeed");
        let direct = serde_json::to_string_pretty(&cert)
            .expect("direct JSON should succeed")
            .into_bytes();
        assert_eq!(via_export, direct);
    }
}
