// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Per-request receive storage limits, independent of proof/work grants.
//! Each retained Record, VCIR dump and erase diagnostic stream has its own
//! eight-MiB aggregate limit (the existing private-input transport scale).
//! Overflow is a refusal/cancellation, never truncated successful output.
use std::io::{self, Read};
pub(crate) const MAX_RECORD_BYTES: usize = 8 * 1024 * 1024;
pub(crate) const MAX_VCIR_BYTES: usize = 8 * 1024 * 1024;
pub(crate) const MAX_ERASE_STDERR_BYTES: usize = 8 * 1024 * 1024;

pub(crate) fn remaining(current: usize, limit: usize) -> io::Result<usize> {
    limit
        .checked_sub(current)
        .ok_or_else(|| io::Error::other("retained output limit exceeded"))
}
pub(crate) fn append(to: &mut Vec<u8>, bytes: &[u8], limit: usize) -> io::Result<()> {
    let next = to
        .len()
        .checked_add(bytes.len())
        .ok_or_else(|| io::Error::other("retained output length overflow"))?;
    if next > limit {
        return Err(io::Error::other("retained output limit exceeded"));
    }
    // Admission precedes reserve/extend. Allocation failure is an ordinary
    // error and the caller still owns its actual child cleanup guard.
    to.try_reserve_exact(bytes.len())
        .map_err(io::Error::other)?;
    to.extend_from_slice(bytes);
    Ok(())
}
pub(crate) fn read(from: &mut impl Read, limit: usize) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    let mut block = [0; 16 * 1024];
    loop {
        let room = remaining(bytes.len(), limit)?;
        if room == 0 {
            let mut extra = [0];
            match from.read(&mut extra) {
                Ok(0) => return Ok(bytes),
                Ok(_) => return Err(io::Error::other("retained output limit exceeded")),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(e),
            }
        }
        let size = room.min(block.len());
        let got = match from.read(&mut block[..size]) {
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            other => other?,
        };
        if got == 0 {
            return Ok(bytes);
        }
        append(&mut bytes, &block[..got], limit)?;
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retained_bytes_preserve_under_and_at_limit_and_reject_before_extend() {
        let mut bytes = Vec::new();
        append(&mut bytes, b"a\0", 3).unwrap();
        assert_eq!(bytes, b"a\0");
        append(&mut bytes, b"z", 3).unwrap();
        assert_eq!(bytes, b"a\0z");
        let capacity = bytes.capacity();
        assert!(append(&mut bytes, b"x", 3).is_err());
        assert_eq!(bytes, b"a\0z");
        assert_eq!(bytes.capacity(), capacity);
        assert_eq!(read(&mut &b"a\0"[..], 3).unwrap(), b"a\0");
        assert_eq!(read(&mut &b"a\0z"[..], 3).unwrap(), b"a\0z");
        assert!(read(&mut &b"a\0zx"[..], 3).is_err());
        assert!(remaining(4, 3).is_err());
    }
    #[test]
    fn read_failure_never_returns_partial_success() {
        struct Broken;
        impl Read for Broken {
            fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
                Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "closed diagnostic stream",
                ))
            }
        }
        assert!(read(&mut Broken, 3).is_err());
    }
}
