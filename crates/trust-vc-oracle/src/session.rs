// trust-vc-oracle — Oracle session manager for multi-round LLM proof synthesis
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Manages session state, conversation history, retry budgets, and session-level
// metrics for multi-round LLM proof synthesis sessions. Each session tracks one
// function through propose-verify-feedback rounds until convergence, divergence,
// timeout, or budget exhaustion.

use std::time::{Duration, Instant, SystemTime};

/// Unique session identifier.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SessionId(String);

impl SessionId {
    /// Create a new session ID from a string.
    #[must_use]
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }

    /// Borrow the inner string.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Display for SessionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Configuration for an oracle session.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SessionConfig {
    /// Maximum number of proposal rounds before the session ends.
    pub max_rounds: usize,
    /// Maximum retries per individual round.
    pub max_retries_per_round: usize,
    /// Overall session timeout.
    pub timeout: Duration,
    /// Improvement score threshold for declaring convergence (0.0 to 1.0).
    pub convergence_threshold: f64,
    /// Minimum improvement rate between rounds to avoid divergence detection.
    pub min_improvement_rate: f64,
    /// Exponential backoff factor for retry delays.
    pub backoff_factor: f64,
}

impl Default for SessionConfig {
    fn default() -> Self {
        Self {
            max_rounds: 10,
            max_retries_per_round: 3,
            timeout: Duration::from_secs(300),
            convergence_threshold: 0.8,
            min_improvement_rate: 0.01,
            backoff_factor: 2.0,
        }
    }
}

/// A single round in the oracle session.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SessionRound {
    /// Which round this is (1-indexed).
    pub round_number: usize,
    /// Which retry attempt within this round (0-indexed).
    pub attempt: usize,
    /// Current status of this round.
    pub status: RoundStatus,
    /// Human-readable summary of the proposal.
    pub proposal_summary: String,
    /// Human-readable summary of the verification feedback.
    pub feedback_summary: String,
    /// Wall-clock time spent in this round.
    pub elapsed: Duration,
    /// Improvement score achieved in this round (0.0 to 1.0).
    pub improvement_score: f64,
}

/// Status of a single round.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
pub enum RoundStatus {
    /// Round created but no proposal yet.
    Pending,
    /// LLM has generated a proposal.
    ProposalGenerated,
    /// Verification is currently running.
    VerificationRunning,
    /// Round completed successfully (verification passed).
    Verified,
    /// Round completed with verification failure.
    Failed,
    /// Round exceeded its time budget.
    Timeout,
    /// Round is being retried.
    Retrying,
}

/// Session-level metrics aggregated across all rounds.
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct SessionMetrics {
    /// Total rounds completed (including retries).
    pub total_rounds: usize,
    /// Rounds that ended in Verified status.
    pub successful_rounds: usize,
    /// Rounds that ended in Failed status.
    pub failed_rounds: usize,
    /// Total retries consumed across all rounds.
    pub total_retries: usize,
    /// Total wall-clock time for the session.
    pub total_elapsed: Duration,
    /// Average time per round.
    pub average_round_time: Duration,
    /// Fraction of rounds that succeeded (0.0 to 1.0).
    pub convergence_rate: f64,
    /// Highest improvement score seen in any round.
    pub best_improvement_score: f64,
    /// Total tokens used across all conversation entries.
    pub tokens_used: usize,
}

/// State machine for the overall session lifecycle.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
pub enum SessionState {
    /// Session created but not yet started.
    Created,
    /// Session is actively running rounds.
    Running,
    /// Session converged (improvement score met threshold).
    Converged,
    /// Session diverged (improvement scores are decreasing).
    Diverged,
    /// Session exceeded its timeout.
    TimedOut,
    /// Session was manually aborted.
    Aborted,
    /// Session failed with an error.
    Failed { reason: String },
}

/// A single entry in the conversation history.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ConversationEntry {
    /// Who authored this entry.
    pub role: ConversationRole,
    /// The text content.
    pub content: String,
    /// When this entry was created.
    pub timestamp: SystemTime,
    /// Estimated token count for this entry.
    pub token_count: usize,
}

/// Role of a conversation participant.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ConversationRole {
    /// System prompt / context.
    System,
    /// User-side input (verification feedback, function source).
    User,
    /// LLM assistant response (proposed annotations).
    Assistant,
    /// Tool call result (verification output).
    Tool,
}

/// Manages retry budgets with exponential backoff.
#[derive(Debug, Clone)]
pub struct RetryBudget {
    max_retries: usize,
    retries_used: usize,
    backoff_factor: f64,
    base_delay: Duration,
}

impl RetryBudget {
    /// Create a new retry budget.
    #[must_use]
    pub fn new(max_retries: usize, backoff_factor: f64, base_delay: Duration) -> Self {
        Self {
            max_retries,
            retries_used: 0,
            backoff_factor,
            base_delay,
        }
    }

    /// Whether another retry is available.
    #[must_use]
    pub fn can_retry(&self) -> bool {
        self.retries_used < self.max_retries
    }

    /// Consume one retry. Returns `Err` if the budget is exhausted.
    pub fn use_retry(&mut self) -> Result<usize, SessionError> {
        if !self.can_retry() {
            return Err(SessionError::RetryBudgetExhausted {
                max_retries: self.max_retries,
            });
        }
        let attempt = self.retries_used;
        self.retries_used += 1;
        Ok(attempt)
    }

    /// Compute the delay before the next retry using exponential backoff.
    ///
    /// `delay = base_delay * backoff_factor ^ retries_used`
    #[must_use]
    pub fn next_delay(&self) -> Duration {
        let multiplier = self.backoff_factor.powi(self.retries_used as i32);
        self.base_delay.mul_f64(multiplier)
    }

    /// Number of retries consumed so far.
    #[must_use]
    pub fn retries_used(&self) -> usize {
        self.retries_used
    }

    /// Maximum retries allowed.
    #[must_use]
    pub fn max_retries(&self) -> usize {
        self.max_retries
    }

    /// Reset the retry budget (e.g., at the start of a new round).
    pub fn reset(&mut self) {
        self.retries_used = 0;
    }
}

/// Errors specific to session management.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
#[non_exhaustive]
pub enum SessionError {
    /// The retry budget has been exhausted.
    #[error("retry budget exhausted after {max_retries} retries")]
    RetryBudgetExhausted { max_retries: usize },
    /// The session is in an invalid state for the requested operation.
    #[error("invalid session state: expected {expected}, got {actual}")]
    InvalidState {
        expected: &'static str,
        actual: String,
    },
    /// The session has timed out.
    #[error("session timed out: elapsed {elapsed:?}, timeout {timeout:?}")]
    TimedOut {
        elapsed: Duration,
        timeout: Duration,
    },
    /// The round budget has been exhausted.
    #[error("round budget exhausted after {max_rounds} rounds")]
    RoundBudgetExhausted { max_rounds: usize },
}

/// Serializable snapshot of a session (excludes non-serializable `Instant`).
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct SessionSnapshot {
    /// Session identifier.
    pub id: SessionId,
    /// Function being verified.
    pub function_name: String,
    /// Current state.
    pub state: SessionState,
    /// All completed rounds.
    pub rounds: Vec<SessionRound>,
    /// Aggregated metrics.
    pub metrics: SessionMetrics,
    /// When the session was created.
    pub created_at: SystemTime,
}

/// The main oracle session manager.
///
/// Tracks the full lifecycle of a multi-round LLM proof synthesis session
/// for a single function: creation, round progression, conversation history,
/// retry budgets, convergence detection, and metric aggregation.
pub struct OracleSession {
    id: SessionId,
    config: SessionConfig,
    state: SessionState,
    rounds: Vec<SessionRound>,
    conversation: Vec<ConversationEntry>,
    metrics: SessionMetrics,
    function_name: String,
    created_at: SystemTime,
    started_at: Option<Instant>,
    retry_budget: RetryBudget,
}

impl OracleSession {
    /// Create a new session for the given function.
    #[must_use]
    pub fn new(function_name: &str, config: SessionConfig) -> Self {
        let id = SessionId::new(format!(
            "{}-{}",
            function_name,
            SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis()
        ));

        let retry_budget = RetryBudget::new(
            config.max_retries_per_round,
            config.backoff_factor,
            Duration::from_millis(100),
        );

        Self {
            id,
            config,
            state: SessionState::Created,
            rounds: Vec::new(),
            conversation: Vec::new(),
            metrics: SessionMetrics::default(),
            function_name: function_name.to_owned(),
            created_at: SystemTime::now(),
            started_at: None,
            retry_budget,
        }
    }

    /// Get the session ID.
    #[must_use]
    pub fn id(&self) -> &SessionId {
        &self.id
    }

    /// Get the current state.
    #[must_use]
    pub fn state(&self) -> &SessionState {
        &self.state
    }

    /// Get the function name.
    #[must_use]
    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    /// Get all completed rounds.
    #[must_use]
    pub fn rounds(&self) -> &[SessionRound] {
        &self.rounds
    }

    /// Begin a new round. Returns the round number (1-indexed).
    ///
    /// Transitions the session to `Running` if it was `Created`.
    /// Resets the per-round retry budget.
    pub fn start_round(&mut self) -> Result<usize, SessionError> {
        // Check timeout first
        if self.is_timed_out() {
            self.state = SessionState::TimedOut;
            return Err(SessionError::TimedOut {
                elapsed: self.elapsed(),
                timeout: self.config.timeout,
            });
        }

        match &self.state {
            SessionState::Created | SessionState::Running => {}
            other => {
                return Err(SessionError::InvalidState {
                    expected: "Created or Running",
                    actual: format!("{:?}", other),
                });
            }
        }

        if self.rounds.len() >= self.config.max_rounds {
            return Err(SessionError::RoundBudgetExhausted {
                max_rounds: self.config.max_rounds,
            });
        }

        // Transition to Running on first round
        if self.state == SessionState::Created {
            self.state = SessionState::Running;
            self.started_at = Some(Instant::now());
        }

        // Reset per-round retry budget
        self.retry_budget.reset();

        let round_number = self.rounds.len() + 1;
        self.rounds.push(SessionRound {
            round_number,
            attempt: 0,
            status: RoundStatus::Pending,
            proposal_summary: String::new(),
            feedback_summary: String::new(),
            elapsed: Duration::ZERO,
            improvement_score: 0.0,
        });

        Ok(round_number)
    }

    /// Record that a proposal was generated for the current round.
    pub fn record_proposal(&mut self, summary: &str) -> Result<(), SessionError> {
        let round = self.current_round_mut()?;
        round.status = RoundStatus::ProposalGenerated;
        round.proposal_summary = summary.to_owned();
        Ok(())
    }

    /// Record the verification result for the current round.
    ///
    /// Updates round status, improvement score, feedback summary, and metrics.
    pub fn record_verification_result(
        &mut self,
        verified: bool,
        improvement_score: f64,
        feedback: &str,
    ) -> Result<(), SessionError> {
        let round = self.current_round_mut()?;
        round.status = if verified {
            RoundStatus::Verified
        } else {
            RoundStatus::Failed
        };
        round.improvement_score = improvement_score;
        round.feedback_summary = feedback.to_owned();

        // Update metrics
        self.metrics.total_rounds += 1;
        if verified {
            self.metrics.successful_rounds += 1;
        } else {
            self.metrics.failed_rounds += 1;
        }
        if improvement_score > self.metrics.best_improvement_score {
            self.metrics.best_improvement_score = improvement_score;
        }

        self.update_aggregate_metrics();
        Ok(())
    }

    /// Check whether the session should continue to the next round.
    ///
    /// Returns `false` if:
    /// - The session has converged (latest improvement >= threshold)
    /// - The session has diverged (improvement scores are decreasing)
    /// - The session has timed out
    /// - The round budget is exhausted
    /// - The session is in a terminal state
    #[must_use]
    pub fn should_continue(&self) -> bool {
        match &self.state {
            SessionState::Running => {}
            SessionState::Created => return true, // hasn't started yet, can start
            _ => return false,                    // terminal state
        }

        if self.is_timed_out() {
            return false;
        }

        if self.rounds.len() >= self.config.max_rounds {
            return false;
        }

        // Check if latest round converged
        if let Some(last) = self.rounds.last() {
            if last.improvement_score >= self.config.convergence_threshold {
                return false;
            }
        }

        // Check for divergence (3+ rounds of decreasing scores)
        !self.is_diverging()
    }

    /// Attempt to use the retry budget for the current round.
    ///
    /// Returns the retry attempt number on success.
    pub fn request_retry(&mut self) -> Result<usize, SessionError> {
        let attempt = self.retry_budget.use_retry()?;
        self.metrics.total_retries += 1;

        if let Some(round) = self.rounds.last_mut() {
            round.status = RoundStatus::Retrying;
            round.attempt = attempt + 1;
        }

        Ok(attempt)
    }

    /// Abort the session with a reason.
    pub fn abort(&mut self, reason: &str) {
        self.state = SessionState::Aborted;
        self.update_aggregate_metrics();
        // Store reason in the last round's feedback if there is one
        if let Some(round) = self.rounds.last_mut() {
            round.feedback_summary = format!("ABORTED: {}", reason);
        }
    }

    /// Create a serializable snapshot of the current session state.
    #[must_use]
    pub fn snapshot(&self) -> SessionSnapshot {
        let mut metrics = self.metrics.clone();
        metrics.total_elapsed = self.elapsed();
        metrics.tokens_used = self.conversation_token_count();

        SessionSnapshot {
            id: self.id.clone(),
            function_name: self.function_name.clone(),
            state: self.state.clone(),
            rounds: self.rounds.clone(),
            metrics,
            created_at: self.created_at,
        }
    }

    /// Get current session metrics.
    #[must_use]
    pub fn metrics(&self) -> &SessionMetrics {
        &self.metrics
    }

    /// Add a conversation history entry.
    pub fn add_conversation_entry(&mut self, role: ConversationRole, content: &str, tokens: usize) {
        self.conversation.push(ConversationEntry {
            role,
            content: content.to_owned(),
            timestamp: SystemTime::now(),
            token_count: tokens,
        });
        self.metrics.tokens_used += tokens;
    }

    /// Total tokens used across all conversation entries.
    #[must_use]
    pub fn conversation_token_count(&self) -> usize {
        self.conversation.iter().map(|e| e.token_count).sum()
    }

    /// Get the conversation history.
    #[must_use]
    pub fn conversation(&self) -> &[ConversationEntry] {
        &self.conversation
    }

    /// Analyze improvement scores for convergence or divergence patterns.
    ///
    /// Transitions the session state to `Converged` or `Diverged` if detected.
    /// Returns the detected state.
    pub fn check_convergence(&mut self) -> &SessionState {
        if self.state != SessionState::Running {
            return &self.state;
        }

        // Check for convergence: latest score meets threshold
        if let Some(last) = self.rounds.last() {
            if last.improvement_score >= self.config.convergence_threshold {
                self.state = SessionState::Converged;
                return &self.state;
            }
        }

        // Check for divergence: 3+ consecutive rounds of decreasing improvement
        if self.is_diverging() {
            self.state = SessionState::Diverged;
            return &self.state;
        }

        // Check timeout
        if self.is_timed_out() {
            self.state = SessionState::TimedOut;
            return &self.state;
        }

        &self.state
    }

    /// Total wall-clock time since the session started.
    ///
    /// Returns `Duration::ZERO` if the session has not started.
    #[must_use]
    pub fn elapsed(&self) -> Duration {
        self.started_at
            .map(|start| start.elapsed())
            .unwrap_or(Duration::ZERO)
    }

    /// Get the retry budget.
    #[must_use]
    pub fn retry_budget(&self) -> &RetryBudget {
        &self.retry_budget
    }

    // --- Private helpers ---

    fn current_round_mut(&mut self) -> Result<&mut SessionRound, SessionError> {
        self.rounds.last_mut().ok_or(SessionError::InvalidState {
            expected: "at least one round started",
            actual: "no rounds".to_owned(),
        })
    }

    fn is_timed_out(&self) -> bool {
        self.started_at
            .map(|start| start.elapsed() >= self.config.timeout)
            .unwrap_or(false)
    }

    fn is_diverging(&self) -> bool {
        let scores: Vec<f64> = self
            .rounds
            .iter()
            .filter(|r| r.status == RoundStatus::Verified || r.status == RoundStatus::Failed)
            .map(|r| r.improvement_score)
            .collect();

        if scores.len() < 3 {
            return false;
        }

        // Check last 3 completed rounds for strictly decreasing scores
        let len = scores.len();
        let recent = &scores[len - 3..];
        recent[0] > recent[1] && recent[1] > recent[2]
    }

    fn update_aggregate_metrics(&mut self) {
        let completed = self
            .rounds
            .iter()
            .filter(|r| r.status == RoundStatus::Verified || r.status == RoundStatus::Failed)
            .count();

        if completed > 0 {
            self.metrics.convergence_rate =
                self.metrics.successful_rounds as f64 / completed as f64;
            self.metrics.average_round_time =
                self.elapsed() / u32::try_from(completed).unwrap_or(u32::MAX);
        }

        self.metrics.total_elapsed = self.elapsed();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn default_config() -> SessionConfig {
        SessionConfig::default()
    }

    fn fast_timeout_config() -> SessionConfig {
        SessionConfig {
            timeout: Duration::from_millis(1),
            ..SessionConfig::default()
        }
    }

    fn small_budget_config() -> SessionConfig {
        SessionConfig {
            max_rounds: 2,
            max_retries_per_round: 1,
            ..SessionConfig::default()
        }
    }

    // --- Session lifecycle tests ---

    #[test]
    fn test_session_new_creates_in_created_state() {
        let session = OracleSession::new("my_func", default_config());
        assert_eq!(*session.state(), SessionState::Created);
        assert_eq!(session.function_name(), "my_func");
        assert!(session.rounds().is_empty());
        assert!(session.id().as_str().starts_with("my_func-"));
    }

    #[test]
    fn test_session_start_round_transitions_to_running() {
        let mut session = OracleSession::new("foo", default_config());
        let round = session.start_round().unwrap();
        assert_eq!(round, 1);
        assert_eq!(*session.state(), SessionState::Running);
        assert_eq!(session.rounds().len(), 1);
        assert_eq!(session.rounds()[0].status, RoundStatus::Pending);
    }

    #[test]
    fn test_session_full_lifecycle_converge() {
        let config = SessionConfig {
            convergence_threshold: 0.8,
            ..default_config()
        };
        let mut session = OracleSession::new("add", config);

        // Round 1: partial success
        session.start_round().unwrap();
        session.record_proposal("requires!(x > 0)").unwrap();
        session
            .record_verification_result(false, 0.3, "postcondition failed")
            .unwrap();
        assert!(session.should_continue());

        // Round 2: better
        session.start_round().unwrap();
        session
            .record_proposal("requires!(x > 0) ensures!(ret > 0)")
            .unwrap();
        session
            .record_verification_result(false, 0.6, "partial verify")
            .unwrap();
        assert!(session.should_continue());

        // Round 3: converged
        session.start_round().unwrap();
        session
            .record_proposal("requires!(x > 0) ensures!(ret == x)")
            .unwrap();
        session
            .record_verification_result(true, 0.9, "verified")
            .unwrap();

        session.check_convergence();
        assert_eq!(*session.state(), SessionState::Converged);
        assert!(!session.should_continue());
    }

    #[test]
    fn test_session_record_proposal_sets_status() {
        let mut session = OracleSession::new("f", default_config());
        session.start_round().unwrap();
        session.record_proposal("ensures!(ret >= 0)").unwrap();
        assert_eq!(session.rounds()[0].status, RoundStatus::ProposalGenerated);
        assert_eq!(session.rounds()[0].proposal_summary, "ensures!(ret >= 0)");
    }

    #[test]
    fn test_session_record_verification_updates_metrics() {
        let mut session = OracleSession::new("g", default_config());
        session.start_round().unwrap();
        session.record_proposal("spec").unwrap();
        session
            .record_verification_result(true, 0.95, "all verified")
            .unwrap();

        let metrics = session.metrics();
        assert_eq!(metrics.total_rounds, 1);
        assert_eq!(metrics.successful_rounds, 1);
        assert_eq!(metrics.failed_rounds, 0);
        assert!((metrics.best_improvement_score - 0.95).abs() < f64::EPSILON);
    }

    // --- Retry budget tests ---

    #[test]
    fn test_retry_budget_new_can_retry() {
        let budget = RetryBudget::new(3, 2.0, Duration::from_millis(100));
        assert!(budget.can_retry());
        assert_eq!(budget.retries_used(), 0);
        assert_eq!(budget.max_retries(), 3);
    }

    #[test]
    fn test_retry_budget_use_retry_increments() {
        let mut budget = RetryBudget::new(3, 2.0, Duration::from_millis(100));
        assert_eq!(budget.use_retry().unwrap(), 0);
        assert_eq!(budget.use_retry().unwrap(), 1);
        assert_eq!(budget.use_retry().unwrap(), 2);
        assert!(!budget.can_retry());
        assert!(budget.use_retry().is_err());
    }

    #[test]
    fn test_retry_budget_exhaustion_error() {
        let mut budget = RetryBudget::new(1, 2.0, Duration::from_millis(100));
        budget.use_retry().unwrap();
        let err = budget.use_retry().unwrap_err();
        assert_eq!(err, SessionError::RetryBudgetExhausted { max_retries: 1 });
    }

    #[test]
    fn test_retry_budget_backoff_calculation() {
        let budget = RetryBudget::new(5, 2.0, Duration::from_millis(100));
        // retries_used = 0 => delay = 100 * 2^0 = 100ms
        assert_eq!(budget.next_delay(), Duration::from_millis(100));

        let mut budget2 = RetryBudget::new(5, 2.0, Duration::from_millis(100));
        budget2.use_retry().unwrap(); // retries_used = 1
                                      // delay = 100 * 2^1 = 200ms
        assert_eq!(budget2.next_delay(), Duration::from_millis(200));

        budget2.use_retry().unwrap(); // retries_used = 2
                                      // delay = 100 * 2^2 = 400ms
        assert_eq!(budget2.next_delay(), Duration::from_millis(400));
    }

    #[test]
    fn test_retry_budget_reset() {
        let mut budget = RetryBudget::new(2, 2.0, Duration::from_millis(100));
        budget.use_retry().unwrap();
        budget.use_retry().unwrap();
        assert!(!budget.can_retry());
        budget.reset();
        assert!(budget.can_retry());
        assert_eq!(budget.retries_used(), 0);
    }

    #[test]
    fn test_session_request_retry_updates_round() {
        let mut session = OracleSession::new("h", default_config());
        session.start_round().unwrap();
        session.record_proposal("spec").unwrap();
        session
            .record_verification_result(false, 0.1, "failed")
            .unwrap();

        let attempt = session.request_retry().unwrap();
        assert_eq!(attempt, 0);
        assert_eq!(
            session.rounds().last().unwrap().status,
            RoundStatus::Retrying
        );
        assert_eq!(session.metrics().total_retries, 1);
    }

    // --- Convergence detection tests ---

    #[test]
    fn test_convergence_detected_when_threshold_met() {
        let config = SessionConfig {
            convergence_threshold: 0.7,
            ..default_config()
        };
        let mut session = OracleSession::new("conv", config);
        session.start_round().unwrap();
        session.record_proposal("spec").unwrap();
        session
            .record_verification_result(true, 0.75, "verified")
            .unwrap();

        let state = session.check_convergence();
        assert_eq!(*state, SessionState::Converged);
    }

    #[test]
    fn test_convergence_not_detected_below_threshold() {
        let config = SessionConfig {
            convergence_threshold: 0.9,
            ..default_config()
        };
        let mut session = OracleSession::new("noconv", config);
        session.start_round().unwrap();
        session.record_proposal("spec").unwrap();
        session
            .record_verification_result(false, 0.5, "partial")
            .unwrap();

        let state = session.check_convergence();
        assert_eq!(*state, SessionState::Running);
    }

    // --- Divergence detection tests ---

    #[test]
    fn test_divergence_detected_with_decreasing_scores() {
        let mut session = OracleSession::new("div", default_config());

        // Three rounds with strictly decreasing scores
        for (i, score) in [0.7, 0.5, 0.3].iter().enumerate() {
            session.start_round().unwrap();
            session.record_proposal(&format!("attempt {}", i)).unwrap();
            session
                .record_verification_result(false, *score, "worse")
                .unwrap();
        }

        let state = session.check_convergence();
        assert_eq!(*state, SessionState::Diverged);
    }

    #[test]
    fn test_no_divergence_with_improving_scores() {
        let mut session = OracleSession::new("imp", default_config());

        for (i, score) in [0.2, 0.4, 0.6].iter().enumerate() {
            session.start_round().unwrap();
            session.record_proposal(&format!("attempt {}", i)).unwrap();
            session
                .record_verification_result(false, *score, "better")
                .unwrap();
        }

        let state = session.check_convergence();
        assert_eq!(*state, SessionState::Running);
    }

    #[test]
    fn test_no_divergence_with_fewer_than_three_rounds() {
        let mut session = OracleSession::new("few", default_config());

        session.start_round().unwrap();
        session.record_proposal("spec").unwrap();
        session
            .record_verification_result(false, 0.5, "partial")
            .unwrap();

        session.start_round().unwrap();
        session.record_proposal("spec2").unwrap();
        session
            .record_verification_result(false, 0.3, "worse")
            .unwrap();

        let state = session.check_convergence();
        assert_eq!(*state, SessionState::Running);
    }

    // --- Timeout tests ---

    #[test]
    fn test_session_timeout_detected() {
        let mut session = OracleSession::new("slow", fast_timeout_config());
        session.start_round().unwrap();
        session.record_proposal("spec").unwrap();

        // Sleep enough for the 1ms timeout to expire
        std::thread::sleep(Duration::from_millis(5));

        session
            .record_verification_result(false, 0.3, "partial")
            .unwrap();
        let state = session.check_convergence();
        assert_eq!(*state, SessionState::TimedOut);
    }

    #[test]
    fn test_session_timeout_prevents_new_round() {
        let mut session = OracleSession::new("timeout_round", fast_timeout_config());
        session.start_round().unwrap();

        std::thread::sleep(Duration::from_millis(5));

        let err = session.start_round().unwrap_err();
        match err {
            SessionError::TimedOut { .. } => {}
            other => panic!("expected TimedOut, got {:?}", other),
        }
    }

    // --- Abort tests ---

    #[test]
    fn test_session_abort() {
        let mut session = OracleSession::new("aborty", default_config());
        session.start_round().unwrap();
        session.record_proposal("spec").unwrap();
        session.abort("user cancelled");

        assert_eq!(*session.state(), SessionState::Aborted);
        assert!(!session.should_continue());
        assert!(session
            .rounds()
            .last()
            .unwrap()
            .feedback_summary
            .contains("ABORTED"));
    }

    #[test]
    fn test_session_abort_prevents_new_round() {
        let mut session = OracleSession::new("abort_block", default_config());
        session.abort("done");

        let err = session.start_round().unwrap_err();
        match err {
            SessionError::InvalidState { .. } => {}
            other => panic!("expected InvalidState, got {:?}", other),
        }
    }

    // --- Snapshot and serialization tests ---

    #[test]
    fn test_snapshot_captures_state() {
        let mut session = OracleSession::new("snap", default_config());
        session.start_round().unwrap();
        session.record_proposal("spec").unwrap();
        session
            .record_verification_result(true, 0.85, "verified")
            .unwrap();

        let snap = session.snapshot();
        assert_eq!(snap.function_name, "snap");
        assert_eq!(snap.state, SessionState::Running);
        assert_eq!(snap.rounds.len(), 1);
        assert_eq!(snap.metrics.successful_rounds, 1);
    }

    #[test]
    fn test_snapshot_serialization_roundtrip() {
        let mut session = OracleSession::new("serde", default_config());
        session.start_round().unwrap();
        session.record_proposal("requires!(x > 0)").unwrap();
        session.record_verification_result(true, 0.9, "ok").unwrap();
        session.add_conversation_entry(ConversationRole::System, "You are a proof oracle.", 15);

        let snap = session.snapshot();
        let json = serde_json::to_string(&snap).expect("serialize");
        let deserialized: SessionSnapshot = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(deserialized.id, snap.id);
        assert_eq!(deserialized.function_name, "serde");
        assert_eq!(deserialized.state, snap.state);
        assert_eq!(deserialized.rounds.len(), 1);
        assert_eq!(deserialized.metrics.successful_rounds, 1);
    }

    // --- Conversation tracking tests ---

    #[test]
    fn test_conversation_entry_tracking() {
        let mut session = OracleSession::new("conv_track", default_config());
        session.add_conversation_entry(ConversationRole::System, "system prompt", 50);
        session.add_conversation_entry(ConversationRole::User, "verify fn add", 20);
        session.add_conversation_entry(ConversationRole::Assistant, "requires!(x > 0)", 30);
        session.add_conversation_entry(ConversationRole::Tool, "verified: true", 10);

        assert_eq!(session.conversation().len(), 4);
        assert_eq!(session.conversation_token_count(), 110);
        assert_eq!(session.conversation()[0].role, ConversationRole::System);
        assert_eq!(session.conversation()[3].role, ConversationRole::Tool);
    }

    #[test]
    fn test_conversation_token_count_empty() {
        let session = OracleSession::new("empty_conv", default_config());
        assert_eq!(session.conversation_token_count(), 0);
    }

    #[test]
    fn test_conversation_tokens_in_metrics() {
        let mut session = OracleSession::new("tok", default_config());
        session.add_conversation_entry(ConversationRole::User, "hello", 100);
        session.add_conversation_entry(ConversationRole::Assistant, "world", 200);

        assert_eq!(session.metrics().tokens_used, 300);
    }

    // --- Multiple rounds with mixed results ---

    #[test]
    fn test_multiple_rounds_mixed_results_metrics() {
        let mut session = OracleSession::new("mixed", default_config());

        // Round 1: fail
        session.start_round().unwrap();
        session.record_proposal("bad spec").unwrap();
        session
            .record_verification_result(false, 0.1, "wrong")
            .unwrap();

        // Round 2: fail (better)
        session.start_round().unwrap();
        session.record_proposal("better spec").unwrap();
        session
            .record_verification_result(false, 0.4, "closer")
            .unwrap();

        // Round 3: success
        session.start_round().unwrap();
        session.record_proposal("good spec").unwrap();
        session
            .record_verification_result(true, 0.95, "verified")
            .unwrap();

        let metrics = session.metrics();
        assert_eq!(metrics.total_rounds, 3);
        assert_eq!(metrics.successful_rounds, 1);
        assert_eq!(metrics.failed_rounds, 2);
        assert!((metrics.best_improvement_score - 0.95).abs() < f64::EPSILON);
        assert!((metrics.convergence_rate - 1.0 / 3.0).abs() < 1e-10);
    }

    // --- Edge cases ---

    #[test]
    fn test_empty_session_should_continue() {
        let session = OracleSession::new("empty", default_config());
        assert!(session.should_continue());
    }

    #[test]
    fn test_single_round_verified_stops() {
        let config = SessionConfig {
            convergence_threshold: 0.5,
            ..default_config()
        };
        let mut session = OracleSession::new("one_shot", config);
        session.start_round().unwrap();
        session.record_proposal("perfect").unwrap();
        session
            .record_verification_result(true, 1.0, "verified")
            .unwrap();

        assert!(!session.should_continue());
    }

    #[test]
    fn test_round_budget_exhaustion() {
        let config = small_budget_config();
        let mut session = OracleSession::new("budget", config);

        session.start_round().unwrap();
        session.record_proposal("s1").unwrap();
        session
            .record_verification_result(false, 0.1, "fail")
            .unwrap();

        session.start_round().unwrap();
        session.record_proposal("s2").unwrap();
        session
            .record_verification_result(false, 0.2, "fail")
            .unwrap();

        let err = session.start_round().unwrap_err();
        match err {
            SessionError::RoundBudgetExhausted { max_rounds: 2 } => {}
            other => panic!("expected RoundBudgetExhausted, got {:?}", other),
        }
        assert!(!session.should_continue());
    }

    #[test]
    fn test_record_proposal_without_round_errors() {
        let mut session = OracleSession::new("no_round", default_config());
        let err = session.record_proposal("spec").unwrap_err();
        match err {
            SessionError::InvalidState { .. } => {}
            other => panic!("expected InvalidState, got {:?}", other),
        }
    }

    #[test]
    fn test_record_verification_without_round_errors() {
        let mut session = OracleSession::new("no_round_v", default_config());
        let err = session
            .record_verification_result(true, 1.0, "ok")
            .unwrap_err();
        match err {
            SessionError::InvalidState { .. } => {}
            other => panic!("expected InvalidState, got {:?}", other),
        }
    }

    #[test]
    fn test_session_elapsed_zero_before_start() {
        let session = OracleSession::new("nostart", default_config());
        assert_eq!(session.elapsed(), Duration::ZERO);
    }

    #[test]
    fn test_session_elapsed_nonzero_after_start() {
        let mut session = OracleSession::new("started", default_config());
        session.start_round().unwrap();
        std::thread::sleep(Duration::from_millis(2));
        assert!(session.elapsed() >= Duration::from_millis(1));
    }

    #[test]
    fn test_session_id_display() {
        let id = SessionId::new("test-session-123");
        assert_eq!(format!("{}", id), "test-session-123");
        assert_eq!(id.as_str(), "test-session-123");
    }

    #[test]
    fn test_session_config_default_values() {
        let config = SessionConfig::default();
        assert_eq!(config.max_rounds, 10);
        assert_eq!(config.max_retries_per_round, 3);
        assert_eq!(config.timeout, Duration::from_secs(300));
        assert!((config.convergence_threshold - 0.8).abs() < f64::EPSILON);
        assert!((config.min_improvement_rate - 0.01).abs() < f64::EPSILON);
        assert!((config.backoff_factor - 2.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_session_state_failed_variant() {
        let mut session = OracleSession::new("fail_state", default_config());
        session.state = SessionState::Failed {
            reason: "internal error".to_owned(),
        };
        assert!(!session.should_continue());
    }

    #[test]
    fn test_session_retry_budget_resets_each_round() {
        let config = SessionConfig {
            max_retries_per_round: 1,
            ..default_config()
        };
        let mut session = OracleSession::new("retry_reset", config);

        // Round 1: use the retry
        session.start_round().unwrap();
        session.record_proposal("s").unwrap();
        session
            .record_verification_result(false, 0.1, "fail")
            .unwrap();
        session.request_retry().unwrap();
        assert!(session.request_retry().is_err());

        // Round 2: budget should be reset
        session.start_round().unwrap();
        session.request_retry().unwrap(); // should succeed
        assert!(session.request_retry().is_err()); // exhausted again
    }

    #[test]
    fn test_retry_budget_zero_max() {
        let mut budget = RetryBudget::new(0, 2.0, Duration::from_millis(100));
        assert!(!budget.can_retry());
        assert!(budget.use_retry().is_err());
    }

    #[test]
    fn test_session_error_display() {
        let err = SessionError::RetryBudgetExhausted { max_retries: 5 };
        assert_eq!(format!("{}", err), "retry budget exhausted after 5 retries");

        let err2 = SessionError::InvalidState {
            expected: "Running",
            actual: "Aborted".to_owned(),
        };
        assert!(format!("{}", err2).contains("Running"));
        assert!(format!("{}", err2).contains("Aborted"));

        let err3 = SessionError::RoundBudgetExhausted { max_rounds: 10 };
        assert!(format!("{}", err3).contains("10"));
    }

    #[test]
    fn test_snapshot_metrics_include_tokens() {
        let mut session = OracleSession::new("tokens_snap", default_config());
        session.add_conversation_entry(ConversationRole::User, "hello", 42);
        session.start_round().unwrap();
        session.record_proposal("s").unwrap();
        session.record_verification_result(true, 0.9, "ok").unwrap();

        let snap = session.snapshot();
        assert_eq!(snap.metrics.tokens_used, 42);
    }

    #[test]
    fn test_session_config_serialization_roundtrip() {
        let config = SessionConfig::default();
        let json = serde_json::to_string(&config).expect("serialize config");
        let deserialized: SessionConfig = serde_json::from_str(&json).expect("deserialize config");
        assert_eq!(deserialized.max_rounds, config.max_rounds);
        assert_eq!(
            deserialized.max_retries_per_round,
            config.max_retries_per_round
        );
        assert!(
            (deserialized.convergence_threshold - config.convergence_threshold).abs()
                < f64::EPSILON
        );
    }
}
