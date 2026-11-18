// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Anonymous native request transport. This module carries data and owns only
//! its own sockets. It never constructs SDK, compiler or resource authority.
//!
//! The coordinator invokes a caller-supplied callback while that caller still
//! borrows its real native owner. Request environment is an explicit output
//! context, never applied to the coordinator's process environment.

use std::ffi::OsString;
use std::io::{self, Read, Write};
use std::os::fd::{AsFd, AsRawFd, BorrowedFd};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::net::{UnixDatagram, UnixStream};
use std::path::PathBuf;
use std::time::Duration;

mod cargo_context;
pub(crate) use cargo_context::CargoContext;
mod control;
mod forwarding;
mod inherit;
pub(crate) use inherit::InheritedChild;
#[cfg(test)]
mod tests;
mod wire;

pub use forwarding::main as forwarding_main;

pub(crate) const INHERITED_CONTROL_ENV: &str = "TRUST_VC_NATIVE_REQUEST_FD";

pub(crate) const MAX_REQUEST_BYTES: usize = 1024 * 1024;
const MAX_ARGUMENTS: usize = 4096;
const MAX_OUTPUT_FRAME: usize = 64 * 1024;
const ADOPTED: [u8; 8] = *b"TVCACK2\0";

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// Only output destinations currently read by the ordinary native shim.
/// Test identity is derived from the original `-o`/entry operands, not a marker.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct OutputContext {
    pub(crate) verdict_dir: Option<PathBuf>,
    pub(crate) dump_vcir: Option<PathBuf>,
}

impl OutputContext {
    pub(crate) fn from_pairs(
        pairs: impl IntoIterator<Item = (OsString, OsString)>,
    ) -> io::Result<Self> {
        let mut result = Self::default();
        for (key, value) in pairs {
            let slot = match key.as_bytes() {
                b"TRUST_VC_VERDICT_DIR" => &mut result.verdict_dir,
                b"TRUST_VC_DUMP_VCIR" => &mut result.dump_vcir,
                _ => return Err(invalid("unrepresented request environment semantics")),
            };
            if slot.is_some() || value.as_bytes().contains(&0) {
                return Err(invalid("duplicate or invalid output context"));
            }
            *slot = Some(PathBuf::from(value));
        }
        Ok(result)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Request {
    /// Complete original argv, including its original executable operand.
    pub(crate) argv: Vec<OsString>,
    pub(crate) cwd: PathBuf,
    pub(crate) outputs: OutputContext,
    /// Original optional macro documentation mode; distinct from output paths.
    pub(crate) verusdoc: Option<OsString>,
    /// Exactly the keys actually consulted by the ordinary Cargo protocol.
    pub(crate) cargo: CargoContext,
    /// Independently read by the genuine macro before its cfg fallback.
    pub(crate) macro_package_name: Option<OsString>,
}

impl Request {
    /// Private worker payload data; decoding never creates a native owner.
    pub(crate) fn encode_data(&self) -> io::Result<Vec<u8>> {
        wire::encode_request(self)
    }
    pub(crate) fn decode_data(bytes: &[u8]) -> io::Result<Self> {
        wire::decode_request(bytes)
    }
}

/// The only shared descendant endpoint. Replies never use this socket.
pub(crate) struct Client {
    control: UnixDatagram,
}

/// A private receiving endpoint, constructed only by `pair`, not a locator.
pub(crate) struct Coordinator {
    control: UnixDatagram,
}

pub(crate) fn pair() -> io::Result<(Coordinator, Client)> {
    let (server, client) = UnixDatagram::pair()?;
    control::no_sigpipe(server.as_fd())?;
    control::no_sigpipe(client.as_fd())?;
    Ok((Coordinator { control: server }, Client { control: client }))
}

impl Client {
    /// Validate and duplicate a real inherited kernel handle. Its descriptor
    /// number locates data transport; it cannot recreate a native owner. The
    /// original descriptor is borrowed and never closed on validation failure.
    pub(crate) fn from_inherited(handle: BorrowedFd<'_>) -> io::Result<Self> {
        control::validate_socket(handle, libc::SOCK_DGRAM)?;
        let copy = handle.try_clone_to_owned()?;
        Ok(Self {
            control: UnixDatagram::from(copy),
        })
    }

    pub(crate) fn submit(&self, request: &Request, admission: Duration) -> io::Result<Response> {
        let deadline = std::time::Instant::now()
            .checked_add(admission)
            .ok_or_else(|| invalid("invalid native admission duration"))?;
        let bytes = wire::encode_request(request)?;
        let (mut local, remote) = UnixStream::pair()?;
        control::no_sigpipe(local.as_fd())?;
        control::no_sigpipe(remote.as_fd())?;
        control::send_until(&self.control, Some(remote.as_fd()), deadline)?;
        // Darwin can discard queued socket data if the sender's only copy of
        // the passed endpoint closes before adoption. Retain it until receipt.
        // This acknowledgement says nothing about imports or compiler success.
        let mut acknowledgement = [0; ADOPTED.len()];
        AdmissionReader {
            socket: &mut local,
            deadline,
        }
        .read_exact(&mut acknowledgement)?;
        if acknowledgement != ADOPTED {
            return Err(invalid("wrong endpoint adoption acknowledgement"));
        }
        drop(remote);
        wire::write_blob(
            &mut AdmissionWriter {
                socket: &mut local,
                deadline,
            },
            &bytes,
        )?;
        local.shutdown(std::net::Shutdown::Write)?;
        local.set_read_timeout(None)?;
        local.set_write_timeout(None)?;
        Ok(Response { socket: local })
    }

    /// Explicit shutdown is required: datagram peers have no stream EOF.
    /// This is a fail-closed stop request, not a native authority grant.
    pub(crate) fn stop(&self) -> io::Result<()> {
        control::send(&self.control, None)
    }
}

impl Coordinator {
    /// Receive exactly one private request endpoint. Timeout bounds transport
    /// admission only; it does not alter compiler, solver or lender limits.
    ///
    /// # Safety
    /// On Darwin, SCM_RIGHTS lacks atomic CLOEXEC reception. The coordinator
    /// must receive between joined callbacks, with no concurrent exec/spawn,
    /// until this method has marked every received descriptor CLOEXEC.
    pub(crate) unsafe fn receive(&self, timeout: Option<Duration>) -> io::Result<Option<Incoming>> {
        self.control.set_read_timeout(timeout)?;
        control::receive(&self.control).map(|socket| socket.map(|socket| Incoming { socket }))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Dispatch {
    Stopped,
    Completed(u8),
}

impl Coordinator {
    /// Invoke only after complete bounded decoding. The callback supplies its
    /// real borrowed owner independently; no request can manufacture that owner.
    ///
    /// # Safety
    /// The same no-concurrent-exec condition as `receive` applies until receipt
    /// has completed. Compiler callbacks must finish and join their workers.
    pub(crate) unsafe fn dispatch(
        &self,
        admission: Duration,
        callback: impl FnOnce(Request, &mut Reply) -> io::Result<u8>,
    ) -> io::Result<Dispatch> {
        // SAFETY: forwarded from this method's native coordinator contract.
        let Some(incoming) = (unsafe { self.receive(Some(admission)) })? else {
            return Ok(Dispatch::Stopped);
        };
        let (request, mut reply) = incoming.read(admission)?;
        let exit = callback(request, &mut reply)?;
        reply.finish(exit)?;
        Ok(Dispatch::Completed(exit))
    }
}

struct AdmissionReader<'socket> {
    socket: &'socket mut UnixStream,
    deadline: std::time::Instant,
}

fn remaining(deadline: std::time::Instant) -> io::Result<Duration> {
    deadline
        .checked_duration_since(std::time::Instant::now())
        .filter(|value| !value.is_zero())
        .map(|value| value.max(Duration::from_micros(1)))
        .ok_or_else(|| io::Error::new(io::ErrorKind::TimedOut, "native request admission deadline"))
}

impl Read for AdmissionReader<'_> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        self.socket
            .set_read_timeout(Some(remaining(self.deadline)?))?;
        self.socket.read(bytes)
    }
}

struct AdmissionWriter<'socket> {
    socket: &'socket mut UnixStream,
    deadline: std::time::Instant,
}

impl Write for AdmissionWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.socket
            .set_write_timeout(Some(remaining(self.deadline)?))?;
        self.socket.write(bytes)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.socket.flush()
    }
}

pub(crate) struct Incoming {
    socket: UnixStream,
}

impl Incoming {
    /// Read a bounded request and require the sender's write EOF. A vanished
    /// or malformed sender never invokes the native callback.
    pub(crate) fn read(mut self, timeout: Duration) -> io::Result<(Request, Reply)> {
        let deadline = std::time::Instant::now()
            .checked_add(timeout)
            .ok_or_else(|| invalid("invalid native admission duration"))?;
        AdmissionWriter {
            socket: &mut self.socket,
            deadline,
        }
        .write_all(&ADOPTED)?;
        let mut admission = AdmissionReader {
            socket: &mut self.socket,
            deadline,
        };
        let bytes = wire::read_blob(&mut admission, MAX_REQUEST_BYTES)?;
        let mut extra = [0; 1];
        if admission.read(&mut extra)? != 0 {
            return Err(invalid("trailing request bytes"));
        }
        let request = wire::decode_request(&bytes)?;
        self.socket.set_read_timeout(None)?;
        self.socket.set_write_timeout(None)?;
        Ok((
            request,
            Reply {
                socket: self.socket,
            },
        ))
    }
}

/// Exclusive response writer. Only a completed final frame permits success.
pub(crate) struct Reply {
    socket: UnixStream,
}

impl Reply {
    pub(crate) fn stdout(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.output(1, bytes)
    }
    pub(crate) fn stderr(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.output(2, bytes)
    }
    fn output(&mut self, kind: u8, bytes: &[u8]) -> io::Result<()> {
        for chunk in bytes.chunks(MAX_OUTPUT_FRAME) {
            self.socket.write_all(&[kind])?;
            wire::write_blob(&mut self.socket, chunk)?;
        }
        Ok(())
    }
    pub(crate) fn finish(mut self, exit: u8) -> io::Result<()> {
        self.socket.write_all(&[3, exit])?;
        // Consuming this writer closes the only received endpoint. A partial
        // callback cannot accidentally return a successful completion frame.
        self.socket.shutdown(std::net::Shutdown::Write)
    }
}

pub(crate) struct Response {
    socket: UnixStream,
}

impl Response {
    pub(crate) fn copy_to(
        mut self,
        stdout: &mut impl Write,
        stderr: &mut impl Write,
    ) -> io::Result<u8> {
        loop {
            let mut kind = [0; 1];
            self.socket.read_exact(&mut kind)?;
            match kind[0] {
                1 | 2 => {
                    let bytes = wire::read_blob(&mut self.socket, MAX_OUTPUT_FRAME)?;
                    if kind[0] == 1 {
                        stdout.write_all(&bytes)?;
                    } else {
                        stderr.write_all(&bytes)?;
                    }
                }
                3 => {
                    let mut exit = [0; 1];
                    self.socket.read_exact(&mut exit)?;
                    let mut extra = [0; 1];
                    if self.socket.read(&mut extra)? != 0 {
                        return Err(invalid("trailing response bytes"));
                    }
                    return Ok(exit[0]);
                }
                _ => return Err(invalid("unknown response frame")),
            }
        }
    }
}
