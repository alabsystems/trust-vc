// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test-side byte framing only. Neither a frame nor its JSON constructs any
//! native compiler, staged-library, import, ownership or verification token.

use serde_json::Value;

type StreamSections<'a> = (&'a [u8], &'a [u8], &'a [u8]);

pub fn split<'a>(raw: &'a [u8], expected: &Value) -> Result<StreamSections<'a>, String> {
    let mut boundary = None;
    let mut offset = 0usize;
    for line in raw.split_inclusive(|byte| *byte == b'\n') {
        if let Ok(value) = serde_json::from_slice::<Value>(line) {
            if value["schema"] == "trust-vc.owned-normal-stream@1" {
                if !line.ends_with(b"\n") {
                    return Err("unterminated owned producer/client boundary".into());
                }
                if boundary.is_some() {
                    return Err("duplicate owned producer/client boundary".into());
                }
                if &value != expected {
                    return Err(
                        "owned producer/client boundary differs from its actual cohort".into(),
                    );
                }
                boundary = Some((offset, offset + line.len()));
            }
        }
        offset += line.len();
    }
    let (start, end) = boundary.ok_or("missing owned producer/client boundary")?;
    Ok((&raw[..start], &raw[start..end], &raw[end..]))
}

pub fn diagnostics(raw: &[u8]) -> Result<Vec<Value>, String> {
    std::str::from_utf8(raw)
        .map_err(|e| e.to_string())?
        .lines()
        .map(|line| serde_json::from_str(line).map_err(|e| e.to_string()))
        .collect()
}
