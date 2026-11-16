// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Closed genuine A40/current-compiler source construction profile. These byte
//! identities select construction inputs; they supply no import/proof authority.

use crate::declaration_alignment::source_bindings::{SourceCompatibility, SourceIdentity};
use crate::declaration_alignment::Digest;

pub(super) const COMPILER: &str = "82bb867eddb94599f68194f701c766f2b6f5a02f";

const MANIFEST: Digest = [
    0x8f, 0xea, 0xfe, 0xb5, 0xb8, 0x90, 0x10, 0x43, 0xb9, 0x0b, 0x8b, 0x51, 0xb7, 0x85, 0x3f, 0x8a,
    0x48, 0x32, 0xd4, 0x4f, 0x2c, 0x59, 0x68, 0x65, 0xb6, 0x8b, 0xad, 0xee, 0xa6, 0x18, 0x04, 0x6b,
];
const RECIPE: Digest = [
    0xc6, 0x5b, 0xa8, 0x79, 0x04, 0xb1, 0x84, 0x2b, 0x1d, 0x60, 0x7b, 0x8a, 0x2b, 0x09, 0xdc, 0x5a,
    0x28, 0x1c, 0x44, 0xe2, 0xad, 0x1d, 0x27, 0x34, 0x06, 0x0f, 0x4c, 0xe7, 0xd4, 0x62, 0x91, 0x50,
];
const PATCH: Digest = [
    0x67, 0xc3, 0xec, 0x8d, 0x35, 0x12, 0x7f, 0x98, 0x53, 0x6f, 0xc0, 0x27, 0x21, 0x09, 0x55, 0x7b,
    0x56, 0x74, 0x05, 0xc0, 0xad, 0x9c, 0xa0, 0xdb, 0x90, 0xbd, 0xbb, 0x03, 0x5b, 0x11, 0xb5, 0x22,
];

pub(super) const SOURCE: SourceIdentity = SourceIdentity {
    manifest_sha256: MANIFEST,
    compatibility: SourceCompatibility::Applied {
        recipe_sha256: RECIPE,
        patch_sha256: PATCH,
    },
};

pub(super) fn check_compiler() -> Result<(), String> {
    if env!("VC_SHIM_COMPILER_COMMIT") != COMPILER {
        return Err(
            "the staging construction profile requires its actual recorded Trust20882 compiler"
                .into(),
        );
    }
    Ok(())
}

pub(super) fn check_source(actual: SourceIdentity) -> Result<(), String> {
    if actual != SOURCE {
        return Err(
            "the source/compatibility inputs are outside the current native construction profile"
                .into(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_source_or_compatibility_identity_is_required() {
        assert!(check_source(SOURCE).is_ok());
        let mut wrong = SOURCE;
        wrong.manifest_sha256[0] ^= 1;
        assert!(check_source(wrong).is_err());
        for part in [0, 1] {
            let mut recipe = RECIPE;
            let mut patch = PATCH;
            if part == 0 {
                recipe[0] ^= 1;
            } else {
                patch[0] ^= 1;
            }
            assert!(check_source(SourceIdentity {
                manifest_sha256: MANIFEST,
                compatibility: SourceCompatibility::Applied {
                    recipe_sha256: recipe,
                    patch_sha256: patch,
                },
            })
            .is_err());
        }
        assert!(check_source(SourceIdentity {
            manifest_sha256: MANIFEST,
            compatibility: SourceCompatibility::Unmodified,
        })
        .is_err());
    }
}
