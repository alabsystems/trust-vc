// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Retain the SHA-approved bytes of the one compiler driver. Every later
//! check still rereads the entire regular file and requires exact equality.
//! This is byte evidence, never a compiler, SDK or import authority token.

use super::PinnedFile;

pub(super) struct ApprovedDriverBytes {
    pin: PinnedFile,
    bytes: Box<[u8]>,
}

impl ApprovedDriverBytes {
    pub(super) fn capture(pin: &PinnedFile) -> Result<Self, String> {
        // The existing SHA pin must approve this actual read before any
        // immutable comparison bytes can be retained.
        let bytes = pin.read()?.into_boxed_slice();
        Ok(Self {
            pin: pin.clone(),
            bytes,
        })
    }

    pub(super) fn revalidate(&self, pin: &PinnedFile) -> Result<(), String> {
        // Preserve PinnedFile::read's absolute/regular/read ordering. No
        // timestamp, inode, cached result or skipped read substitutes for bytes.
        if !pin.path.is_absolute() {
            return Err("a pinned input path must be absolute".into());
        }
        let metadata = std::fs::metadata(&pin.path).map_err(|error| error.to_string())?;
        if !metadata.is_file() {
            return Err("a pinned input is not a regular file".into());
        }
        let bytes = std::fs::read(&pin.path).map_err(|error| error.to_string())?;
        if pin.path != self.pin.path || pin.sha256 != self.pin.sha256 {
            return Err("the approved compiler-driver pin changed".into());
        }
        if bytes.as_slice() != self.bytes.as_ref() {
            return Err("pinned input bytes changed".into());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn driver_bytes_require_sha_approval_and_recheck_changes_and_paths() {
        // Ordinary byte mechanics only: this never constructs a BuiltCohort.
        let root = std::env::temp_dir()
            .join(".ubd")
            .join(format!("trust-vc-driver-bytes-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let root = root.canonicalize().unwrap();
        let path = root.join("original");
        let original = b"original ordinary driver byte-comparison control";
        std::fs::write(&path, original).unwrap();
        let pin = PinnedFile {
            path,
            sha256: super::super::digest(original),
        };
        let approved = ApprovedDriverBytes::capture(&pin).unwrap();
        assert!(approved.revalidate(&pin).is_ok());
        let mut changed = original.to_vec();
        changed[0] ^= 1;
        std::fs::write(&pin.path, &changed).unwrap();
        assert!(approved.revalidate(&pin).is_err());
        assert!(ApprovedDriverBytes::capture(&pin).is_err());
        std::fs::write(&pin.path, original).unwrap();
        assert!(approved.revalidate(&pin).is_ok());
        let mut other = pin.clone();
        other.path = root.join("same-bytes-other-path");
        std::fs::write(&other.path, original).unwrap();
        assert!(approved.revalidate(&other).is_err());
        other = pin.clone();
        other.sha256[0] ^= 1;
        assert!(approved.revalidate(&other).is_err());
        other = pin.clone();
        other.path = root.clone();
        assert!(approved.revalidate(&other).is_err());
        std::fs::remove_dir_all(root).unwrap();
    }
}
