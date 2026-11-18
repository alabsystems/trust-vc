// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual direct children stay owned across pipe errors and unwinding.
#[cfg(test)]
use std::io::Read;
use std::io::{self, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, ExitStatus};

pub(crate) struct RetainedChild {
    child: Option<Child>,
    #[cfg(test)]
    joined: Option<std::sync::mpsc::SyncSender<ExitStatus>>,
}

// A failed OS wait is not evidence of termination. Never return or unwind
// through the live owner in that state, and never reconstruct a PID handle.
fn unknown_join() -> ! {
    loop {
        std::thread::park();
    }
}

impl RetainedChild {
    pub(crate) fn spawn(command: &mut Command) -> io::Result<Self> {
        command.spawn().map(|child| Self {
            child: Some(child),
            #[cfg(test)]
            joined: None,
        })
    }
    pub(crate) fn take_stdin(&mut self) -> io::Result<ChildStdin> {
        self.child
            .as_mut()
            .and_then(|c| c.stdin.take())
            .ok_or_else(|| io::Error::other("child has no owned stdin"))
    }
    pub(crate) fn take_stdout(&mut self) -> io::Result<ChildStdout> {
        self.child
            .as_mut()
            .and_then(|c| c.stdout.take())
            .ok_or_else(|| io::Error::other("child has no owned stdout"))
    }
    pub(crate) fn write_input(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.take_stdin()?.write_all(bytes)
    }
    pub(crate) fn wait(&mut self) -> ExitStatus {
        let child = self.child.as_mut().expect("owned child already joined");
        child.stdin.take();
        let status = match child.wait() {
            Ok(status) => status,
            Err(_) => unknown_join(),
        };
        #[cfg(test)]
        if let Some(observer) = self.joined.take() {
            // Observation ONLY: this value comes directly from the successful
            // actual wait above. It neither represents nor grants custody.
            let _ = observer.send(status.clone());
        }
        self.child.take();
        status
    }
    pub(crate) fn stderr_and_wait(&mut self) -> io::Result<(ExitStatus, Vec<u8>)> {
        let result = match self.child.as_mut().and_then(|c| c.stderr.take()) {
            Some(mut stderr) => crate::retained_bytes::read(
                &mut stderr,
                crate::retained_bytes::MAX_ERASE_STDERR_BYTES,
            ),
            None => Err(io::Error::other("child has no owned stderr")),
        };
        if let Err(error) = result {
            self.cancel();
            return Err(error);
        }
        Ok((self.wait(), result.unwrap()))
    }
    pub(crate) fn cancel(&mut self) -> Option<ExitStatus> {
        if let Some(child) = self.child.as_mut() {
            child.stdin.take();
            child.stdout.take();
            child.stderr.take();
            // A failed kill is not a join; the actual wait is still required.
            let _ = child.kill();
            return Some(self.wait());
        }
        None
    }
}
impl Drop for RetainedChild {
    fn drop(&mut self) {
        self.cancel();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Stdio;
    #[test]
    fn stderr_and_nonzero_status_come_from_the_actual_join() {
        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", "printf actual-stderr >&2; exit 7"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped());
        let mut child = RetainedChild::spawn(&mut command).unwrap();
        let (status, bytes) = child.stderr_and_wait().unwrap();
        assert_eq!(status.code(), Some(7));
        assert_eq!(bytes, b"actual-stderr");
        assert!(child.child.is_none());
    }
    #[test]
    fn failed_live_input_cancel_and_signal_keep_the_child_until_actual_wait() {
        use std::os::unix::process::ExitStatusExt;
        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", "exec 0<&-; printf closed >&2; while :; do :; done"])
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::piped());
        let mut child = RetainedChild::spawn(&mut command).unwrap();
        let mut ready = [0; 6];
        child
            .child
            .as_mut()
            .unwrap()
            .stderr
            .as_mut()
            .unwrap()
            .read_exact(&mut ready)
            .unwrap();
        assert_eq!(&ready, b"closed");
        assert!(child.write_input(b"no receiver").is_err());
        let status = child.cancel().unwrap();
        assert_eq!(status.signal(), Some(libc::SIGKILL));
        assert!(child.child.is_none());
    }
    #[test]
    fn unwinding_observes_actual_join_before_the_outer_scope_is_released() {
        use std::sync::{
            atomic::{AtomicBool, Ordering},
            mpsc, Arc,
        };
        struct OuterScope {
            receiver: mpsc::Receiver<ExitStatus>,
            observed: Arc<AtomicBool>,
        }
        impl Drop for OuterScope {
            fn drop(&mut self) {
                // This receiver is independent of the cleanup guard and is read
                // BEFORE the outer scope finishes unwinding. No PID polling or
                // marker substitutes for the guard's actual Child::wait result.
                self.observed
                    .store(self.receiver.try_recv().is_ok(), Ordering::SeqCst);
            }
        }
        let (sender, receiver) = mpsc::sync_channel(1);
        let observed = Arc::new(AtomicBool::new(false));
        let outer_observed = observed.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
            let _outer = OuterScope {
                receiver,
                observed: outer_observed,
            };
            let mut command = Command::new("/bin/sh");
            command
                .args(["-c", "read value"])
                .stdin(Stdio::piped())
                .stdout(Stdio::null())
                .stderr(Stdio::piped());
            let mut child = RetainedChild::spawn(&mut command).unwrap();
            child.joined = Some(sender);
            panic!("actual cleanup boundary");
        }));
        assert!(result.is_err());
        assert!(
            observed.load(Ordering::SeqCst),
            "outer scope returned without observing an actual terminal wait"
        );
    }
    #[test]
    fn actual_stderr_at_limit_is_exact_and_over_limit_cancels_and_joins() {
        let limit = crate::retained_bytes::MAX_ERASE_STDERR_BYTES;
        for size in [limit - 1, limit, limit + 1] {
            let mut command = Command::new("/bin/sh");
            command
                .args(["-c", &format!("printf '%{size}s' x >&2")])
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::piped());
            let mut child = RetainedChild::spawn(&mut command).unwrap();
            let result = child.stderr_and_wait();
            assert!(child.child.is_none());
            if size <= limit {
                let (status, bytes) = result.unwrap();
                assert!(status.success());
                assert_eq!(bytes.len(), size);
                assert_eq!(bytes.last(), Some(&b'x'));
                assert!(bytes[..size - 1].iter().all(|b| *b == b' '));
            } else {
                assert!(result.is_err());
            }
        }
    }
}
