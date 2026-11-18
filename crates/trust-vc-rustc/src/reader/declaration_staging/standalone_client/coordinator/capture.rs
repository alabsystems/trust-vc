// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Capture the actual native compiler's bytes, including its erase children.
//! This is a dedicated serial process boundary, not a diagnostic reformatter.

use std::fs::{File, OpenOptions};
use std::io::{self, Seek, SeekFrom, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::path::Path;

struct Saved {
    stdout: OwnedFd,
    stderr: OwnedFd,
    cwd: File,
    restored: bool,
}

fn duplicate(fd: i32) -> io::Result<OwnedFd> {
    // SAFETY: fcntl duplicates a standard descriptor as an independently owned,
    // close-on-exec descriptor; it does not borrow any resource or request FD.
    let copy = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) };
    if copy < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(unsafe { OwnedFd::from_raw_fd(copy) })
    }
}

fn replace(source: i32, destination: i32) -> io::Result<()> {
    // SAFETY: caller retains the source; destination is one standard I/O slot.
    if unsafe { libc::dup2(source, destination) } < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

fn flush() -> io::Result<()> {
    io::stdout().flush()?;
    io::stderr().flush()
}

impl Saved {
    fn restore(&mut self) -> io::Result<()> {
        flush()?;
        replace(self.stdout.as_raw_fd(), libc::STDOUT_FILENO)?;
        replace(self.stderr.as_raw_fd(), libc::STDERR_FILENO)?;
        // SAFETY: cwd is the still-owned actual original directory description.
        if unsafe { libc::fchdir(self.cwd.as_raw_fd()) } < 0 {
            return Err(io::Error::last_os_error());
        }
        self.restored = true;
        Ok(())
    }
}

impl Drop for Saved {
    fn drop(&mut self) {
        if !self.restored && self.restore().is_err() {
            // A process with a stale output/cwd context cannot serve another
            // caller or publish a successful response.
            std::process::abort();
        }
    }
}

/// # Safety
/// No other same-process thread may use cwd/stdio or spawn while they are
/// redirected. The callback must finish and join all native child work.
pub(crate) unsafe fn run<T>(
    root: &Path,
    phase: &str,
    cwd: &Path,
    callback: impl FnOnce() -> T,
) -> io::Result<(T, File, File)> {
    if !cwd.is_absolute() || cwd.canonicalize()? != cwd || !cwd.is_dir() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "native request cwd must be its actual canonical directory",
        ));
    }
    let mut stdout = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(root.join(format!("{phase}.stdout")))?;
    let mut stderr = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(root.join(format!("{phase}.stderr")))?;
    flush()?;
    let mut saved = Saved {
        stdout: duplicate(libc::STDOUT_FILENO)?,
        stderr: duplicate(libc::STDERR_FILENO)?,
        cwd: File::open(".")?,
        restored: false,
    };
    std::env::set_current_dir(cwd)?;
    replace(stdout.as_raw_fd(), libc::STDOUT_FILENO)?;
    replace(stderr.as_raw_fd(), libc::STDERR_FILENO)?;
    let result = callback();
    saved.restore()?;
    stdout.seek(SeekFrom::Start(0))?;
    stderr.seek(SeekFrom::Start(0))?;
    Ok((result, stdout, stderr))
}

// These are copies of the two actual standard DATA pipes, never caller FDs.
pub(crate) fn standard_data_pipes() -> io::Result<(File, File)> {
    Ok((
        File::from(duplicate(libc::STDIN_FILENO)?),
        File::from(duplicate(libc::STDOUT_FILENO)?),
    ))
}
