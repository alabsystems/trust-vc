// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded frames on the actual private worker's stdin/stdout, data only.
use std::io::{self, Read, Write};

pub(crate) const INITIAL: u8 = 0;
pub(crate) const STDOUT: u8 = 1;
pub(crate) const STDERR: u8 = 2;
pub(crate) const RECORD: u8 = 3;
pub(crate) const VCIR: u8 = 4;
pub(crate) const ERASE: u8 = 5;
pub(crate) const COMPLETE: u8 = 6;
pub(crate) const ERASE_BYTES: u8 = 11;
pub(crate) const ERASE_END: u8 = 12;
pub(crate) const MAX_INPUT: usize = crate::native_requests::MAX_REQUEST_BYTES * 8;
const CHUNK: usize = 16 * 1024;

pub(crate) fn frame(to: &mut impl Write, tag: u8, bytes: &[u8]) -> io::Result<()> {
    if bytes.len() > MAX_INPUT {
        return Err(io::Error::other("oversize worker frame"));
    }
    to.write_all(&[tag])?;
    to.write_all(&(bytes.len() as u32).to_be_bytes())?;
    to.write_all(bytes)?;
    to.flush()
}
pub(crate) fn receive(from: &mut impl Read) -> io::Result<Option<(u8, Vec<u8>)>> {
    receive_limited(from, |_| Ok(MAX_INPUT))
}
pub(crate) fn receive_limited(
    from: &mut impl Read,
    limit: impl FnOnce(u8) -> io::Result<usize>,
) -> io::Result<Option<(u8, Vec<u8>)>> {
    let mut tag = [0];
    loop {
        match from.read(&mut tag) {
            Ok(0) => return Ok(None),
            Ok(_) => break,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
    let mut size = [0; 4];
    from.read_exact(&mut size)?;
    let size = u32::from_be_bytes(size) as usize;
    if size > MAX_INPUT || size > limit(tag[0])? {
        return Err(io::Error::other(
            "worker frame exceeds remaining receive storage",
        ));
    }
    let mut bytes = Vec::new();
    bytes.try_reserve_exact(size).map_err(io::Error::other)?;
    bytes.resize(size, 0);
    from.read_exact(&mut bytes)?;
    Ok(Some((tag[0], bytes)))
}
/// After completion no frame is legal. Probe only one stack byte, retrying
/// Interrupted. Never parse a header, allocate a payload or retain trailing
/// bytes while the completed request's aggregate buffers are still live.
pub(crate) fn expect_eof(from: &mut impl Read) -> io::Result<()> {
    let mut byte = [0; 1];
    loop {
        match from.read(&mut byte) {
            Ok(0) => return Ok(()),
            Ok(_) => return Err(io::ErrorKind::InvalidData.into()),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
}

pub(crate) fn bytes(to: &mut impl Write, tag: u8, bytes: &[u8]) -> io::Result<()> {
    for chunk in bytes.chunks(CHUNK) {
        frame(to, tag, chunk)?;
    }
    Ok(())
}
pub(crate) fn stream(to: &mut impl Write, tag: u8, from: &mut impl Read) -> io::Result<()> {
    let mut buf = [0; CHUNK];
    loop {
        let size = from.read(&mut buf)?;
        if size == 0 {
            return Ok(());
        }
        frame(to, tag, &buf[..size])?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn framed_data_keeps_bytes_and_refuses_truncation_and_oversize() {
        let mut bytes = Vec::new();
        frame(&mut bytes, STDOUT, b"a\0b").unwrap();
        assert_eq!(
            receive(&mut &bytes[..]).unwrap(),
            Some((STDOUT, b"a\0b".to_vec()))
        );
        for cut in 1..bytes.len() {
            assert!(receive(&mut &bytes[..cut]).is_err());
        }
        let mut oversized = vec![ERASE];
        oversized.extend_from_slice(&((MAX_INPUT as u32) + 1).to_be_bytes());
        assert!(receive(&mut &oversized[..]).is_err());
    }
    #[test]
    fn frame_write_failure_is_not_completion() {
        struct Broken;
        impl Write for Broken {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "actual writer closed",
                ))
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        assert!(frame(&mut Broken, COMPLETE, &[0, 0]).is_err());
        let mut bytes = Vec::new();
        frame(&mut bytes, ERASE_END, &0i32.to_be_bytes()).unwrap();
        frame(&mut bytes, ERASE_END, &0i32.to_be_bytes()).unwrap();
        let mut cursor = &bytes[..];
        assert!(receive(&mut cursor).unwrap().is_some());
        assert!(receive(&mut cursor).unwrap().is_some());
        // Framing never interprets a response as an owner/completion grant.
    }
    #[test]
    fn aggregate_receive_admission_precedes_payload_allocation_or_read() {
        use crate::retained_bytes::{
            append, MAX_ERASE_STDERR_BYTES, MAX_RECORD_BYTES, MAX_VCIR_BYTES,
        };
        for tag in [RECORD, VCIR, ERASE_BYTES] {
            let mut header = vec![tag];
            header.extend_from_slice(&2u32.to_be_bytes());
            let error = receive_limited(&mut &header[..], |_| Ok(1)).unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::Other); // not missing-payload EOF
            let mut received = Vec::new();
            append(&mut received, b"ab", 3).unwrap();
            let mut frame_bytes = Vec::new();
            frame(&mut frame_bytes, tag, b"c").unwrap();
            let (_, bytes) = receive_limited(&mut &frame_bytes[..], |_| Ok(3 - received.len()))
                .unwrap()
                .unwrap();
            append(&mut received, &bytes, 3).unwrap();
            assert_eq!(received, b"abc");
            assert!(receive_limited(&mut &frame_bytes[..], |_| Ok(3 - received.len())).is_err());
        }
        assert_eq!(MAX_RECORD_BYTES, MAX_INPUT);
        assert_eq!(MAX_VCIR_BYTES, MAX_INPUT);
        assert_eq!(MAX_ERASE_STDERR_BYTES, MAX_INPUT);
    }
    #[test]
    fn final_eof_probe_never_reads_a_header_or_payload_and_retries_interrupts() {
        struct Probe<'a> {
            data: &'a [u8],
            reads: usize,
            consumed: usize,
            interrupts: usize,
            error: Option<io::ErrorKind>,
        }
        impl Read for Probe<'_> {
            fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
                assert_eq!(out.len(), 1, "EOF admission requested more than one byte");
                self.reads += 1;
                if self.interrupts > 0 {
                    self.interrupts -= 1;
                    return Err(io::ErrorKind::Interrupted.into());
                }
                if let Some(error) = self.error {
                    return Err(error.into());
                }
                if self.data.is_empty() {
                    return Ok(0);
                }
                out[0] = self.data[0];
                self.data = &self.data[1..];
                self.consumed += 1;
                Ok(1)
            }
        }
        let mut eof = Probe {
            data: b"",
            reads: 0,
            consumed: 0,
            interrupts: 0,
            error: None,
        };
        expect_eof(&mut eof).unwrap();
        assert_eq!((eof.reads, eof.consumed), (1, 0));
        let mut trailing = Probe {
            data: b"\x03\xff\xff\xff\xffforbidden-payload",
            reads: 0,
            consumed: 0,
            interrupts: 0,
            error: None,
        };
        assert_eq!(
            expect_eof(&mut trailing).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        assert_eq!((trailing.reads, trailing.consumed), (1, 1));
        assert_eq!(trailing.data, b"\xff\xff\xff\xffforbidden-payload");
        let mut interrupted = Probe {
            data: b"",
            reads: 0,
            consumed: 0,
            interrupts: 2,
            error: None,
        };
        expect_eof(&mut interrupted).unwrap();
        assert_eq!((interrupted.reads, interrupted.consumed), (3, 0));
        let mut interrupted_trailing = Probe {
            data: b"abcd",
            reads: 0,
            consumed: 0,
            interrupts: 1,
            error: None,
        };
        assert_eq!(
            expect_eof(&mut interrupted_trailing).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        assert_eq!(
            (interrupted_trailing.reads, interrupted_trailing.consumed),
            (2, 1)
        );
        assert_eq!(interrupted_trailing.data, b"bcd");
        let mut broken = Probe {
            data: b"not-read",
            reads: 0,
            consumed: 0,
            interrupts: 0,
            error: Some(io::ErrorKind::BrokenPipe),
        };
        assert_eq!(
            expect_eof(&mut broken).unwrap_err().kind(),
            io::ErrorKind::BrokenPipe
        );
        assert_eq!((broken.reads, broken.consumed), (1, 0));
        assert_eq!(broken.data, b"not-read");
    }
}
