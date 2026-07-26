// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use serde_json;
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{
    CertificateMetadata, Literal, TheoryLemmaKind, TrustVcProofCertificate, WireClause,
    WireClauseId, WireResolutionStep, WireTheoryLemma, BINARY_FORMAT_VERSION, BINARY_MAGIC,
    CERTIFICATE_VERSION, MIN_BINARY_HEADER_LEN,
};

const SECTION_INPUT_CLAUSES: u8 = 0x01;
const SECTION_THEORY_LEMMAS: u8 = 0x02;
const SECTION_RESOLUTION_STEPS: u8 = 0x03;
const SECTION_METADATA: u8 = 0x04;
const SECTION_END: u8 = 0xFF;

/// Errors arising from certificate serialization and parsing.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum FormatError {
    /// Wire format version is not supported by this build.
    #[error(
        "unsupported certificate version {found}; this build supports versions 1-{max_supported}"
    )]
    UnsupportedVersion { found: u32, max_supported: u32 },

    /// JSON serialization or deserialization failure.
    #[error("JSON codec error: {0}")]
    Json(#[from] serde_json::Error),

    /// Binary serialization or deserialization failure.
    #[error("binary codec error: {0}")]
    Binary(String),

    /// The binary payload is too short to contain the required header.
    #[error("binary payload too short: expected at least {expected} bytes, got {actual}")]
    BinaryTooShort { expected: usize, actual: usize },

    /// The binary payload does not start with the expected magic bytes.
    #[error("invalid binary magic: expected {expected:?}, got {actual:?}")]
    InvalidMagic { expected: [u8; 4], actual: [u8; 4] },
}

type Result<T> = std::result::Result<T, FormatError>;

impl TrustVcProofCertificate {
    /// Reject certificates whose version exceeds what this build supports.
    #[must_use = "version check result must be inspected"]
    pub fn enforce_supported_version(&self) -> Result<()> {
        if !(1..=CERTIFICATE_VERSION).contains(&self.version) {
            return Err(FormatError::UnsupportedVersion {
                found: self.version,
                max_supported: CERTIFICATE_VERSION,
            });
        }
        Ok(())
    }

    /// Serialize to pretty-printed JSON.
    #[must_use = "serialized JSON should be consumed"]
    pub fn to_json(&self) -> Result<String> {
        self.enforce_supported_version()?;
        serde_json::to_string_pretty(self).map_err(FormatError::Json)
    }

    /// Deserialize from a JSON string, enforcing version checks.
    #[must_use = "deserialized certificate should be used"]
    pub fn from_json(s: &str) -> Result<Self> {
        let cert: Self = serde_json::from_str(s)?;
        cert.enforce_supported_version()?;
        Ok(cert)
    }

    /// Serialize to the compact binary representation.
    #[must_use = "serialized bytes should be consumed"]
    pub fn to_bytes(&self) -> Result<Vec<u8>> {
        self.enforce_supported_version()?;

        let mut buf = Vec::new();
        buf.extend_from_slice(&BINARY_MAGIC);
        buf.push(BINARY_FORMAT_VERSION);
        encode_varint(&mut buf, self.version as u64);
        buf.extend_from_slice(&self.source_hash);
        buf.extend_from_slice(&self.vc_hash);
        encode_varint(&mut buf, self.empty_clause_id.0);

        buf.push(SECTION_INPUT_CLAUSES);
        encode_varint(&mut buf, self.input_clauses.len() as u64);
        for clause in &self.input_clauses {
            encode_clause(&mut buf, clause);
        }

        buf.push(SECTION_THEORY_LEMMAS);
        encode_varint(&mut buf, self.theory_lemmas.len() as u64);
        for lemma in &self.theory_lemmas {
            encode_theory_lemma(&mut buf, lemma);
        }

        buf.push(SECTION_RESOLUTION_STEPS);
        encode_varint(&mut buf, self.resolution_steps.len() as u64);
        for step in &self.resolution_steps {
            encode_resolution_step(&mut buf, step);
        }

        buf.push(SECTION_METADATA);
        encode_string(&mut buf, &self.metadata.timestamp);
        encode_string(&mut buf, &self.metadata.trust_vc_version);
        encode_string(&mut buf, &self.metadata.solver_version);

        buf.push(SECTION_END);
        Ok(buf)
    }

    /// Deserialize from the compact binary representation.
    #[must_use = "deserialized certificate should be used"]
    pub fn from_bytes(data: &[u8]) -> Result<Self> {
        if data.len() < MIN_BINARY_HEADER_LEN {
            return Err(FormatError::BinaryTooShort {
                expected: MIN_BINARY_HEADER_LEN,
                actual: data.len(),
            });
        }

        let mut magic = [0u8; 4];
        magic.copy_from_slice(&data[..BINARY_MAGIC.len()]);
        if magic != BINARY_MAGIC {
            return Err(FormatError::InvalidMagic {
                expected: BINARY_MAGIC,
                actual: magic,
            });
        }

        let mut pos = BINARY_MAGIC.len();
        let binary_version = data[pos];
        pos += 1;
        if binary_version != BINARY_FORMAT_VERSION {
            return Err(FormatError::Binary(format!(
                "unsupported binary format version {binary_version} (expected {BINARY_FORMAT_VERSION})"
            )));
        }

        let (version_raw, used) = decode_varint(&data[pos..])?;
        pos += used;
        let version = u32::try_from(version_raw).map_err(|_| FormatError::UnsupportedVersion {
            found: u32::MAX,
            max_supported: CERTIFICATE_VERSION,
        })?;
        if !(1..=CERTIFICATE_VERSION).contains(&version) {
            return Err(FormatError::UnsupportedVersion {
                found: version,
                max_supported: CERTIFICATE_VERSION,
            });
        }

        if pos + 64 > data.len() {
            return Err(FormatError::BinaryTooShort {
                expected: pos + 64,
                actual: data.len(),
            });
        }

        let mut source_hash = [0u8; 32];
        source_hash.copy_from_slice(&data[pos..pos + 32]);
        pos += 32;

        let mut vc_hash = [0u8; 32];
        vc_hash.copy_from_slice(&data[pos..pos + 32]);
        pos += 32;

        let (empty_clause_id, used) = decode_varint(&data[pos..])?;
        pos += used;

        let mut input_clauses = Vec::new();
        let mut theory_lemmas = Vec::new();
        let mut resolution_steps = Vec::new();
        let mut metadata = CertificateMetadata {
            timestamp: String::new(),
            trust_vc_version: String::new(),
            solver_version: String::new(),
        };

        loop {
            if pos >= data.len() {
                return Err(FormatError::Binary("unexpected end of data".to_string()));
            }

            let tag = data[pos];
            pos += 1;

            if tag == SECTION_END {
                break;
            }

            match tag {
                SECTION_INPUT_CLAUSES => {
                    let (count, used) = decode_len(&data[pos..], "input clause count")?;
                    pos += used;
                    for _ in 0..count {
                        let (clause, used) = decode_clause(&data[pos..])?;
                        pos += used;
                        input_clauses.push(clause);
                    }
                }
                SECTION_THEORY_LEMMAS => {
                    let (count, used) = decode_len(&data[pos..], "theory lemma count")?;
                    pos += used;
                    for _ in 0..count {
                        let (lemma, used) = decode_theory_lemma(&data[pos..])?;
                        pos += used;
                        theory_lemmas.push(lemma);
                    }
                }
                SECTION_RESOLUTION_STEPS => {
                    let (count, used) = decode_len(&data[pos..], "resolution step count")?;
                    pos += used;
                    for _ in 0..count {
                        let (step, used) = decode_resolution_step(&data[pos..])?;
                        pos += used;
                        resolution_steps.push(step);
                    }
                }
                SECTION_METADATA => {
                    let (timestamp, used) = decode_string(&data[pos..], "metadata timestamp")?;
                    pos += used;
                    let (trust_vc_version, used) =
                        decode_string(&data[pos..], "metadata trust_vc version")?;
                    pos += used;
                    let (solver_version, used) =
                        decode_string(&data[pos..], "metadata solver version")?;
                    pos += used;
                    metadata = CertificateMetadata {
                        timestamp,
                        trust_vc_version,
                        solver_version,
                    };
                }
                other => {
                    return Err(FormatError::Binary(format!(
                        "unknown section tag 0x{other:02x}"
                    )));
                }
            }
        }

        let cert = Self {
            version,
            source_hash,
            vc_hash,
            resolution_steps,
            theory_lemmas,
            input_clauses,
            empty_clause_id: WireClauseId(empty_clause_id),
            metadata,
        };
        cert.enforce_supported_version()?;
        Ok(cert)
    }

    /// Hex-encoded SHA-256 source hash for display.
    #[must_use]
    pub fn source_hash_hex(&self) -> String {
        hex_encode(&self.source_hash)
    }

    /// Hex-encoded SHA-256 VC hash for display.
    #[must_use]
    pub fn vc_hash_hex(&self) -> String {
        hex_encode(&self.vc_hash)
    }
}

/// Compute SHA-256 of the given bytes and return the digest.
#[must_use]
pub fn sha256(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&result);
    out
}

fn encode_clause(buf: &mut Vec<u8>, clause: &WireClause) {
    encode_varint(buf, clause.id.0);
    encode_varint(buf, clause.literals.len() as u64);
    for lit in &clause.literals {
        encode_signed(buf, lit.0);
    }
}

fn decode_clause(data: &[u8]) -> Result<(WireClause, usize)> {
    let mut pos = 0;
    let (id, used) = decode_varint(&data[pos..])?;
    pos += used;
    let (lit_count, used) = decode_len(&data[pos..], "clause literal count")?;
    pos += used;
    let mut literals = Vec::with_capacity(lit_count);
    for _ in 0..lit_count {
        let (lit, used) = decode_signed(&data[pos..])?;
        pos += used;
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

fn encode_theory_lemma(buf: &mut Vec<u8>, lemma: &WireTheoryLemma) {
    encode_varint(buf, lemma.id.0);
    buf.push(theory_kind_to_byte(lemma.kind));
    encode_varint(buf, lemma.literals.len() as u64);
    for lit in &lemma.literals {
        encode_signed(buf, lit.0);
    }
    match &lemma.justification {
        Some(justification) => encode_string(buf, justification),
        None => encode_varint(buf, 0),
    }
}

fn decode_theory_lemma(data: &[u8]) -> Result<(WireTheoryLemma, usize)> {
    let mut pos = 0;
    let (id, used) = decode_varint(&data[pos..])?;
    pos += used;
    let kind = *data
        .get(pos)
        .ok_or_else(|| FormatError::Binary("unexpected end reading theory kind".to_string()))?;
    pos += 1;
    let (lit_count, used) = decode_len(&data[pos..], "theory lemma literal count")?;
    pos += used;
    let mut literals = Vec::with_capacity(lit_count);
    for _ in 0..lit_count {
        let (lit, used) = decode_signed(&data[pos..])?;
        pos += used;
        literals.push(Literal(lit));
    }
    let (justification, used) = decode_string(&data[pos..], "theory lemma justification")?;
    pos += used;
    Ok((
        WireTheoryLemma {
            id: WireClauseId(id),
            kind: theory_kind_from_byte(kind)?,
            literals,
            justification: (!justification.is_empty()).then_some(justification),
        },
        pos,
    ))
}

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

fn decode_resolution_step(data: &[u8]) -> Result<(WireResolutionStep, usize)> {
    let mut pos = 0;
    let (result_id, used) = decode_varint(&data[pos..])?;
    pos += used;
    let (antecedent_a, used) = decode_varint(&data[pos..])?;
    pos += used;
    let (antecedent_b, used) = decode_varint(&data[pos..])?;
    pos += used;
    let (pivot, used) = decode_signed(&data[pos..])?;
    pos += used;
    let (lit_count, used) = decode_len(&data[pos..], "resolution literal count")?;
    pos += used;
    let mut result_literals = Vec::with_capacity(lit_count);
    for _ in 0..lit_count {
        let (lit, used) = decode_signed(&data[pos..])?;
        pos += used;
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

fn encode_string(buf: &mut Vec<u8>, s: &str) {
    encode_varint(buf, s.len() as u64);
    buf.extend_from_slice(s.as_bytes());
}

fn decode_string(data: &[u8], field: &str) -> Result<(String, usize)> {
    let (len, used) = decode_len(data, field)?;
    let end = used + len;
    if data.len() < end {
        return Err(FormatError::Binary(format!(
            "unexpected end reading {field}"
        )));
    }
    let value = std::str::from_utf8(&data[used..end])
        .map_err(|e| FormatError::Binary(format!("invalid UTF-8 in {field}: {e}")))?;
    Ok((value.to_string(), end))
}

fn encode_varint(buf: &mut Vec<u8>, mut value: u64) {
    loop {
        let byte = (value & 0x7F) as u8;
        value >>= 7;
        if value == 0 {
            buf.push(byte);
            return;
        }
        buf.push(byte | 0x80);
    }
}

fn decode_varint(data: &[u8]) -> Result<(u64, usize)> {
    let mut value = 0u64;
    let mut shift = 0;

    for (index, byte) in data.iter().copied().enumerate() {
        value |= u64::from(byte & 0x7F) << shift;
        if byte & 0x80 == 0 {
            return Ok((value, index + 1));
        }
        shift += 7;
        if shift >= 64 {
            return Err(FormatError::Binary("varint too long".to_string()));
        }
    }

    Err(FormatError::Binary(
        "unexpected end of data while decoding varint".to_string(),
    ))
}

fn decode_len(data: &[u8], field: &str) -> Result<(usize, usize)> {
    let (value, used) = decode_varint(data)?;
    let len = usize::try_from(value)
        .map_err(|_| FormatError::Binary(format!("{field} exceeds usize: {value}")))?;
    Ok((len, used))
}

fn encode_signed(buf: &mut Vec<u8>, value: i64) {
    let zigzag = ((value << 1) ^ (value >> 63)) as u64;
    encode_varint(buf, zigzag);
}

fn decode_signed(data: &[u8]) -> Result<(i64, usize)> {
    let (zigzag, used) = decode_varint(data)?;
    let value = ((zigzag >> 1) as i64) ^ (-((zigzag & 1) as i64));
    Ok((value, used))
}

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

fn theory_kind_from_byte(value: u8) -> Result<TheoryLemmaKind> {
    match value {
        0 => Ok(TheoryLemmaKind::Euf),
        1 => Ok(TheoryLemmaKind::Lra),
        2 => Ok(TheoryLemmaKind::Nia),
        3 => Ok(TheoryLemmaKind::BitVector),
        4 => Ok(TheoryLemmaKind::Array),
        5 => Ok(TheoryLemmaKind::Sequence),
        6 => Ok(TheoryLemmaKind::Other),
        other => Err(FormatError::Binary(format!(
            "unknown theory kind tag {other}"
        ))),
    }
}

use crate::hex_encode;
