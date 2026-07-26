// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod oracle;
mod program;
mod targets;

pub use oracle::{verify_generated_program, VerificationOutcome};
pub use program::GeneratedProgram;
pub use targets::{
    collections_contradiction_program, ensures_false_program, mode_crossing_program,
    strict_inequality_program,
};

pub fn assert_not_verified(case: GeneratedProgram) {
    verify_generated_program(case).assert_not_verified();
}

#[cfg(test)]
mod tests {
    use super::{
        collections_contradiction_program, ensures_false_program, mode_crossing_program,
        strict_inequality_program, verify_generated_program,
    };

    fn assert_fail_closed(
        label: &str,
        seeds: &[&[u8]],
        build: fn(&[u8]) -> super::GeneratedProgram,
    ) {
        for seed in seeds {
            let outcome = verify_generated_program(build(seed));
            assert!(
                !outcome.is_false_verified(),
                "{label} produced a false-Verified outcome: {}",
                outcome.status()
            );
        }
    }

    #[test]
    fn ensures_false_samples_never_verify() {
        assert_fail_closed(
            "ensures_false",
            &[b"", b"\x01\x02\x03", b"\xff\x10\x20\x30"],
            ensures_false_program,
        );
    }

    #[test]
    fn strict_inequality_samples_never_verify() {
        assert_fail_closed(
            "strict_inequality",
            &[b"", b"\x05\x06", b"\x7f\x80\x81"],
            strict_inequality_program,
        );
    }

    #[test]
    fn mode_crossing_variants_never_verify() {
        assert_fail_closed(
            "mode_crossing",
            &[b"\x00", b"\x01", b"\x02", b"\x03"],
            mode_crossing_program,
        );
    }

    #[test]
    fn collection_variants_never_verify() {
        assert_fail_closed(
            "collections_contradiction",
            &[
                b"\x00", b"\x01", b"\x02", b"\x03", b"\x04", b"\x05", b"\x06",
            ],
            collections_contradiction_program,
        );
    }
}
