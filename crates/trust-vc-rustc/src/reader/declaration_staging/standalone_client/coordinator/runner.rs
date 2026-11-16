// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The maintained suite runner owns descendants and observes its stdin lease.
//! Closing that lease requests cleanup; join it before releasing the SDK owner.

use crate::native_requests::{Client, InheritedChild};
use std::io;
use std::process::{Command, ExitStatus, Stdio};

pub(super) struct Runner {
    child: Option<InheritedChild>,
}

impl Runner {
    pub(super) fn spawn(client: &Client, mut command: Command) -> io::Result<Self> {
        command.stdin(Stdio::piped());
        Ok(Self {
            child: Some(client.spawn(command)?),
        })
    }

    pub(super) fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        self.child.as_mut().unwrap().try_wait()
    }

    pub(super) fn wait(mut self) -> io::Result<ExitStatus> {
        self.child.take().unwrap().wait()
    }
}

impl Drop for Runner {
    fn drop(&mut self) {
        if let Some(mut child) = self.child.take() {
            child.close_stdin();
            if child.wait().is_err() {
                // Continuing after an unknown runner lifetime would violate
                // the dedicated coordinator's joined-worker contract.
                std::process::abort();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_stdin_lease_closes_and_joins_normal_and_cancelled_children() {
        let root = std::env::temp_dir().join(format!("trust-vc-runner-{}", std::process::id()));
        std::fs::create_dir(&root).unwrap();
        for cancel in [false, true] {
            let output = root.join(if cancel {
                "cancelled.stdout"
            } else {
                "normal.stdout"
            });
            let (_server, client) = crate::native_requests::pair().unwrap();
            let mut command = Command::new("/bin/sh");
            command
                .args([
                    "-c",
                    "read value; printf 'stdin closed'; exit 7",
                    "--owned-stdin",
                ])
                .stdout(std::fs::File::create(&output).unwrap());
            let mut runner = Runner::spawn(&client, command).unwrap();
            // The child cannot pass its read while our actual pipe is open.
            assert!(runner.try_wait().unwrap().is_none());
            if cancel {
                drop(runner); // closes the real lease and directly waits
            } else {
                runner.child.as_mut().unwrap().close_stdin();
                assert_eq!(runner.wait().unwrap().code(), Some(7));
            }
            assert_eq!(std::fs::read(output).unwrap(), b"stdin closed");
        }
        std::fs::remove_dir_all(root).unwrap();
    }
}
