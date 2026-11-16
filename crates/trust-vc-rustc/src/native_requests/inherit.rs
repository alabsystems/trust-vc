// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::os::unix::process::CommandExt;
use std::process::{Child, Command, ExitStatus};

/// A child started with one genuine inherited control endpoint. Dropping an
/// unfinished child kills and waits it; callers can retain the actual status.
pub(crate) struct InheritedChild {
    child: Option<Child>,
}

impl Client {
    /// Consume the command, so a retained pre_exec closure can never outlive
    /// this descriptor and later clear CLOEXEC on a reused unrelated FD.
    /// This adds only a channel locator. Genuine resource setup remains the
    /// caller's existing responsibility and is never synthesized here.
    pub(crate) fn spawn(&self, mut command: Command) -> io::Result<InheritedChild> {
        let inherited = self.control.as_fd().try_clone_to_owned()?;
        let fd = inherited.as_raw_fd();
        command.env(INHERITED_CONTROL_ENV, fd.to_string());
        // SAFETY: pre_exec performs only fcntl on the still-owned descriptor.
        unsafe {
            command.pre_exec(move || {
                let flags = libc::fcntl(fd, libc::F_GETFD);
                if flags < 0 || libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0 {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let child = command.spawn();
        drop(command);
        drop(inherited);
        child.map(|child| InheritedChild { child: Some(child) })
    }
}

impl InheritedChild {
    pub(crate) fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        self.child.as_mut().unwrap().try_wait()
    }

    pub(crate) fn close_stdin(&mut self) {
        self.child.as_mut().unwrap().stdin.take();
    }

    pub(crate) fn wait(mut self) -> io::Result<ExitStatus> {
        let status = self.child.as_mut().unwrap().wait()?;
        self.child.take();
        Ok(status)
    }
}

impl Drop for InheritedChild {
    fn drop(&mut self) {
        if let Some(child) = self.child.as_mut() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}
