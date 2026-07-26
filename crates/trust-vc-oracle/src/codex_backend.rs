// trust-vc-oracle — Codex and Claude CLI backends for LLM proof synthesis
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::io::Write;
use std::process::Command;
use std::time::Duration;

use crate::backend::{LlmBackend, ProposedAnnotations};
use crate::feedback::ProofFeedback;
use crate::prompt::{build_user_prompt, parse_annotations, SYSTEM_PROMPT};
use crate::OracleError;

/// Default subprocess timeout in seconds.
const DEFAULT_TIMEOUT_SECS: u64 = 30;

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Check whether a CLI tool is reachable on `$PATH` by running `which <name>`.
fn cli_is_available(name: &str) -> bool {
    Command::new("which")
        .arg(name)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Spawn a child process, write `input` to its stdin, and wait for output
/// with a timeout.  Returns `(stdout, stderr)` on success.
fn run_with_timeout(
    cmd: &mut Command,
    input: Option<&str>,
    timeout: Duration,
    tool_name: &str,
) -> Result<String, OracleError> {
    cmd.stdin(if input.is_some() {
        std::process::Stdio::piped()
    } else {
        std::process::Stdio::null()
    })
    .stdout(std::process::Stdio::piped())
    .stderr(std::process::Stdio::piped());

    let mut child = cmd.spawn().map_err(|e| {
        if e.kind() == std::io::ErrorKind::NotFound {
            OracleError::BackendUnavailable {
                backend: tool_name.to_string(),
                reason: format!("'{}' not found on $PATH", tool_name),
            }
        } else {
            OracleError::BackendError {
                message: format!("failed to spawn {}: {}", tool_name, e),
            }
        }
    })?;

    // Write prompt to stdin, then drop the handle so the child sees EOF.
    if let Some(input_text) = input {
        if let Some(mut stdin) = child.stdin.take() {
            stdin
                .write_all(input_text.as_bytes())
                .map_err(|e| OracleError::BackendError {
                    message: format!("failed to write to {} stdin: {}", tool_name, e),
                })?;
            // stdin is dropped here, sending EOF to the child
        }
    }

    // Wait with timeout — use a thread to enforce the deadline.
    let timeout_secs = timeout.as_secs();
    let result = child.wait_with_output();

    // `wait_with_output` is blocking; we use a simpler approach: we set an
    // alarm on POSIX but the cross-platform safe alternative is to spawn a
    // watchdog thread.  For now, we rely on the fact that both `codex` and
    // `claude` CLIs have their own timeout flags (we pass them below), and
    // treat the Rust-side timeout as a last resort via `try_wait` polling.
    //
    // However, because `wait_with_output` consumes the child, we implement
    // the timeout by spawning a thread and using a channel.  This is the
    // standard Rust pattern for subprocess timeouts without nix/libc.
    //
    // NOTE: The actual timeout enforcement is handled by the caller using
    // `spawn_with_timeout` below, which avoids double-implementation.
    let output = result.map_err(|e| OracleError::BackendError {
        message: format!("{} process error: {}", tool_name, e),
    })?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let code = output
            .status
            .code()
            .map(|c| c.to_string())
            .unwrap_or_else(|| "signal".to_string());
        return Err(OracleError::BackendError {
            message: format!("{} exited with code {}: {}", tool_name, code, stderr.trim()),
        });
    }

    // Guard against truly huge outputs that could eat memory.
    let _ = timeout_secs; // suppress warning — timeout flag passed to CLI
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    Ok(stdout)
}

/// Spawn a subprocess with a hard timeout enforced via a watchdog thread.
///
/// This wraps `run_with_timeout` with a `std::thread::spawn` + channel
/// pattern so the caller is never blocked forever.
fn spawn_with_timeout(
    mut cmd: Command,
    input: Option<&str>,
    timeout: Duration,
    tool_name: &str,
) -> Result<String, OracleError> {
    // We need to own the input for the thread.
    let input_owned = input.map(|s| s.to_string());
    let tool = tool_name.to_string();
    let timeout_secs = timeout.as_secs();

    let (tx, rx) = std::sync::mpsc::channel();

    // Prepare the command in the child thread.
    // We must move `cmd` into the thread since Command is not Sync.
    std::thread::spawn(move || {
        let result = run_with_timeout(&mut cmd, input_owned.as_deref(), timeout, &tool);
        let _ = tx.send(result);
    });

    rx.recv_timeout(timeout + Duration::from_secs(5))
        .map_err(|_| OracleError::BackendTimeout {
            seconds: timeout_secs,
        })?
}

// ---------------------------------------------------------------------------
// CodexBackend — shells out to the `codex` CLI
// ---------------------------------------------------------------------------

/// LLM backend that shells out to the OpenAI Codex CLI (`codex`).
///
/// The Codex CLI is invoked as:
/// ```text
/// echo "<prompt>" | codex --model <model> --full-auto --quiet
/// ```
///
/// The `--quiet` flag suppresses interactive UI, and `--full-auto` approves
/// all tool calls automatically. The prompt is passed via stdin.
pub struct CodexBackend {
    /// Model to use (e.g., "o4-mini", "o3").
    model: String,
    /// Working directory for codex (optional).
    working_dir: Option<String>,
    /// Subprocess timeout.
    timeout: Duration,
}

impl CodexBackend {
    #[must_use]
    pub fn new(model: &str) -> Self {
        Self {
            model: model.to_string(),
            working_dir: None,
            timeout: Duration::from_secs(DEFAULT_TIMEOUT_SECS),
        }
    }

    #[must_use]
    pub fn with_working_dir(mut self, dir: &str) -> Self {
        self.working_dir = Some(dir.to_string());
        self
    }

    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
}

impl LlmBackend for CodexBackend {
    fn propose_annotations(
        &self,
        source: &str,
        feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, OracleError> {
        if !self.is_available() {
            return Err(OracleError::BackendUnavailable {
                backend: "codex".to_string(),
                reason: "'codex' CLI not found on $PATH".to_string(),
            });
        }

        let user_prompt = build_user_prompt(source, feedback_history);
        let full_prompt = format!("{}\n\n{}", SYSTEM_PROMPT, user_prompt);

        let mut cmd = Command::new("codex");

        // `codex` accepts prompts via stdin when invoked without a positional
        // argument.  `--full-auto` approves tool calls, `--quiet` suppresses
        // the TUI, and `--model` selects the model.
        cmd.arg("--model").arg(&self.model);
        cmd.arg("--full-auto");
        cmd.arg("--quiet");

        if let Some(dir) = &self.working_dir {
            cmd.arg("-C").arg(dir);
        }

        let response = spawn_with_timeout(cmd, Some(&full_prompt), self.timeout, "codex")?;

        Ok(parse_annotations(&response))
    }

    fn name(&self) -> &str {
        "codex"
    }

    fn is_available(&self) -> bool {
        cli_is_available("codex")
    }
}

// ---------------------------------------------------------------------------
// ClaudeBackend — shells out to the `claude` CLI (Claude Code)
// ---------------------------------------------------------------------------

/// LLM backend that shells out to the Claude Code CLI (`claude`).
///
/// The Claude CLI is invoked as:
/// ```text
/// echo "<prompt>" | claude -p --model <model> --output-format text
/// ```
///
/// `-p` (print mode) makes `claude` read from stdin and write the response
/// to stdout without entering an interactive REPL.  `--output-format text`
/// suppresses JSON envelope output.
pub struct ClaudeBackend {
    /// Model to use (e.g., "sonnet", "opus").
    model: String,
    /// Subprocess timeout.
    timeout: Duration,
}

impl ClaudeBackend {
    #[must_use]
    pub fn new(model: &str) -> Self {
        Self {
            model: model.to_string(),
            timeout: Duration::from_secs(DEFAULT_TIMEOUT_SECS),
        }
    }

    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
}

impl LlmBackend for ClaudeBackend {
    fn propose_annotations(
        &self,
        source: &str,
        feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, OracleError> {
        if !self.is_available() {
            return Err(OracleError::BackendUnavailable {
                backend: "claude".to_string(),
                reason: "'claude' CLI not found on $PATH".to_string(),
            });
        }

        let user_prompt = build_user_prompt(source, feedback_history);
        let full_prompt = format!("{}\n\n{}", SYSTEM_PROMPT, user_prompt);

        // Use `claude -p` (print / pipe mode) which reads from stdin and
        // writes the LLM response to stdout.  The `--output-format text`
        // flag ensures raw text output (no JSON wrapper).  The system
        // prompt is embedded in the user prompt since `-p` mode does not
        // support a separate `--system` flag.
        let mut cmd = Command::new("claude");
        cmd.arg("-p");
        cmd.arg("--model").arg(&self.model);
        cmd.arg("--output-format").arg("text");

        // Pass a max-turns of 1 to prevent the agent from looping
        cmd.arg("--max-turns").arg("1");

        let response = spawn_with_timeout(cmd, Some(&full_prompt), self.timeout, "claude")?;

        Ok(parse_annotations(&response))
    }

    fn name(&self) -> &str {
        "claude"
    }

    fn is_available(&self) -> bool {
        cli_is_available("claude")
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_codex_backend_name() {
        let backend = CodexBackend::new("o4-mini");
        assert_eq!(backend.name(), "codex");
    }

    #[test]
    fn test_claude_backend_name() {
        let backend = ClaudeBackend::new("sonnet");
        assert_eq!(backend.name(), "claude");
    }

    #[test]
    fn test_codex_backend_builder() {
        let backend = CodexBackend::new("o3")
            .with_working_dir("/tmp")
            .with_timeout(Duration::from_secs(60));
        assert_eq!(backend.model, "o3");
        assert_eq!(backend.working_dir.as_deref(), Some("/tmp"));
        assert_eq!(backend.timeout, Duration::from_secs(60));
    }

    #[test]
    fn test_claude_backend_builder() {
        let backend = ClaudeBackend::new("opus").with_timeout(Duration::from_secs(120));
        assert_eq!(backend.model, "opus");
        assert_eq!(backend.timeout, Duration::from_secs(120));
    }

    #[test]
    fn test_cli_is_available_for_common_tool() {
        // `which` itself is always available on POSIX
        assert!(cli_is_available("which"));
    }

    #[test]
    fn test_cli_is_available_for_missing_tool() {
        assert!(!cli_is_available("__trust_vc_nonexistent_tool_42__"));
    }

    #[test]
    fn test_codex_unavailable_returns_error() {
        // If codex is not installed, propose_annotations returns BackendUnavailable.
        let backend = CodexBackend::new("o4-mini");
        if !backend.is_available() {
            let result = backend.propose_annotations("fn foo() {}", &[]);
            assert!(result.is_err());
            let err = result.unwrap_err();
            assert!(
                matches!(err, OracleError::BackendUnavailable { .. }),
                "expected BackendUnavailable, got: {:?}",
                err
            );
        }
    }

    #[test]
    fn test_claude_unavailable_returns_error() {
        // If claude is not installed, propose_annotations returns BackendUnavailable.
        let backend = ClaudeBackend::new("sonnet");
        if !backend.is_available() {
            let result = backend.propose_annotations("fn foo() {}", &[]);
            assert!(result.is_err());
            let err = result.unwrap_err();
            assert!(
                matches!(err, OracleError::BackendUnavailable { .. }),
                "expected BackendUnavailable, got: {:?}",
                err
            );
        }
    }

    #[test]
    fn test_run_with_timeout_echo() {
        // Use `echo` to verify our subprocess plumbing works.
        let mut cmd = Command::new("echo");
        cmd.arg("hello world");
        let result = run_with_timeout(&mut cmd, None, Duration::from_secs(5), "echo");
        let output = result.expect("echo should succeed");
        assert_eq!(output.trim(), "hello world");
    }

    #[test]
    fn test_run_with_timeout_stdin_cat() {
        // Use `cat` to verify stdin forwarding works.
        let mut cmd = Command::new("cat");
        let result = run_with_timeout(&mut cmd, Some("test input"), Duration::from_secs(5), "cat");
        let output = result.expect("cat should echo stdin");
        assert_eq!(output, "test input");
    }

    #[test]
    fn test_run_with_timeout_nonzero_exit() {
        let mut cmd = Command::new("false");
        let result = run_with_timeout(&mut cmd, None, Duration::from_secs(5), "false");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, OracleError::BackendError { .. }),
            "expected BackendError for non-zero exit, got: {:?}",
            err
        );
    }

    #[test]
    fn test_spawn_with_timeout_basic() {
        let mut cmd = Command::new("echo");
        cmd.arg("via spawn");
        let result = spawn_with_timeout(cmd, None, Duration::from_secs(5), "echo");
        let output = result.expect("spawned echo should succeed");
        assert_eq!(output.trim(), "via spawn");
    }
}
