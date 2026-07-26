//! Verification error catalog — human-readable explanations for error codes.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

/// An entry in the error catalog with a code, short name, and detailed explanation.
pub struct ErrorEntry {
    pub code: &'static str,
    pub short: &'static str,
    pub explanation: &'static str,
    pub suggestion: &'static str,
}

pub const CATALOG: &[ErrorEntry] = &[
    ErrorEntry {
        code: "E001",
        short: "Assertion failed",
        explanation: concat!(
            "In formal verification, an assertion is not just a runtime check; it is a claim ",
            "that must be true on every execution the solver considers. TrustVc proves that ",
            "claim against all inputs allowed by your `requires!` clauses, branch conditions, ",
            "and earlier facts. This error means the solver found a counterexample where the ",
            "assertion could be false. For example, if you write `ensures!(result > 0)` but a ",
            "branch can return `0`, the solver can pick that branch and show `result = 0`.",
        ),
        suggestion: concat!(
            "Either strengthen the assumptions so the bad case cannot happen, such as ",
            "`requires!(x != 0)` or a guarding `if`, or weaken the claim to match the behavior ",
            "you actually implement. A common repair is changing `ensures!(result > 0)` to ",
            "`ensures!(result >= 0)` when zero is a legitimate result.",
        ),
    },
    ErrorEntry {
        code: "E002",
        short: "Overflow detected",
        explanation: concat!(
            "TrustVc checks arithmetic against the real bounds of the Rust type, not against ",
            "idealized unbounded integers. This error means the solver found inputs where an ",
            "addition, subtraction, multiplication, or similar operation would leave the valid ",
            "range of the type. For example, `fn add_one(x: i32) -> i32 { x + 1 }` is not safe ",
            "for all `i32` values because the solver can choose `x = i32::MAX`. The same issue ",
            "appears with code like `x - 1` when `x` could be `0` for an unsigned type.",
        ),
        suggestion: concat!(
            "Add explicit bounds such as `requires!(x < i32::MAX)` before `x + 1` or ",
            "`requires!(x > 0)` before `x - 1`. If wraparound or clamping is intentional, use ",
            "`wrapping_add`, `checked_add`, or `saturating_add` so the verifier sees the ",
            "semantics you actually want.",
        ),
    },
    ErrorEntry {
        code: "E003",
        short: "Division by zero",
        explanation: concat!(
            "A verifier must prove that every division and remainder uses a nonzero divisor on ",
            "every reachable path. This error means the solver found a path where the divisor ",
            "could be `0`. For example, `fn ratio(x: i32, y: i32) -> i32 { x / y }` fails unless ",
            "you tell TrustVc something about `y`, because the solver is free to choose `y = 0`. ",
            "The same reasoning applies to `%`, even when the divisor becomes zero only after a ",
            "local computation.",
        ),
        suggestion: concat!(
            "Establish the fact right before the operation with a contract like ",
            "`requires!(y != 0)` or a guard such as `if y == 0 { return 0; }`. When the divisor ",
            "is computed, use a pattern like `let d = denom(x); assert!(d != 0); x / d` so the ",
            "proof obligation is attached to the exact value being used.",
        ),
    },
    ErrorEntry {
        code: "E004",
        short: "Shift out of range",
        explanation: concat!(
            "Bit shifts are only defined when the shift amount is inside the valid range for the ",
            "operand's bit width. This error means the solver can make the shift amount negative ",
            "or at least as large as the number of bits in the value being shifted. For example, ",
            "`x << n` on a `u32` needs proof that `0 <= n` and `n < 32`; otherwise the solver can ",
            "choose `n = 32` and reject the proof. This often appears when `n` comes from input ",
            "data or another calculation instead of a fixed constant.",
        ),
        suggestion: concat!(
            "Constrain the amount with a precondition such as `requires!(n < 32)` for `u32`, or ",
            "normalize it explicitly with a branch or modulo when that matches the algorithm. A ",
            "common pattern is `let s = n % 32; x << s`, but only use that rewrite when reducing ",
            "the shift count is actually the intended semantics.",
        ),
    },
    ErrorEntry {
        code: "E005",
        short: "Loop invariant not established",
        explanation: concat!(
            "A loop invariant is a fact that must already be true before the first iteration ",
            "starts, not just something that becomes true after the loop runs for a while. This ",
            "error means TrustVc could not prove the invariant from the state immediately before ",
            "the loop. For example, `invariant!(0 <= i && i <= n)` is not established if `i` ",
            "starts at `-1`, even if the loop body increments `i` right away. The solver is ",
            "telling you that the loop's starting state does not match the story your invariant ",
            "claims.",
        ),
        suggestion: concat!(
            "Initialize the loop variables so the invariant is true on entry, or state a weaker ",
            "invariant that matches the real initial state. Typical fixes are `let mut i = 0;` ",
            "before a counting loop, an assertion right before the loop that records a needed ",
            "fact, or a `requires!` clause guaranteeing the variables begin in range.",
        ),
    },
    ErrorEntry {
        code: "E006",
        short: "Loop invariant not preserved",
        explanation: concat!(
            "A loop invariant must still be true after one full execution of the loop body ",
            "whenever the loop continues. This error means the solver found a state where the ",
            "invariant holds at the top of the loop but can fail after the body runs once. For ",
            "example, with `invariant!(0 <= i && i <= n)`, a body like `i += step` is not ",
            "preserved if `step` could be `2` and `n` could be `1`, because the solver can reach ",
            "`i = 2`. Usually this means the update logic and the invariant describe different ",
            "ranges.",
        ),
        suggestion: concat!(
            "Make the body re-establish the invariant on every pass, or strengthen the invariant ",
            "with the facts the update needs. Common patterns are changing `i += step` to ",
            "`i += 1`, adding bounds like `requires!(step > 0 && step <= n - i)`, or widening ",
            "the invariant so it matches the range the loop actually maintains.",
        ),
    },
    ErrorEntry {
        code: "E007",
        short: "Decreases check failed",
        explanation: concat!(
            "TrustVc tries to prove that recursive calls and loops eventually stop, and it does ",
            "that with a decreases measure. That measure must get strictly smaller on every ",
            "recursive call or loop back-edge and must have a lower bound. For example, ",
            "`fn countdown(n: i32) { if n > 0 { countdown(n); } }` fails because the recursive ",
            "call makes no progress, and even `countdown(n - 1)` needs proof that `n` stays in a ",
            "sensible range. When you see this error, the solver is saying it cannot yet prove ",
            "termination.",
        ),
        suggestion: concat!(
            "Choose a measure that obviously moves toward zero, such as `decreases!(n)` for ",
            "`countdown(n - 1)` or `decreases!(xs.len() - i)` for an index loop. Then make the ",
            "progress explicit with patterns like `i += 1`, `n - 1`, or recursive calls on ",
            "`&xs[1..]`, and add bounds like `requires!(n >= 0)` so the measure cannot decrease ",
            "forever.",
        ),
    },
    ErrorEntry {
        code: "E008",
        short: "Precondition violated",
        explanation: concat!(
            "A precondition is a promise the caller must establish before the callee is allowed ",
            "to assume it. This error means a call site may reach a function without satisfying ",
            "that function's `requires!` clause. For example, if `safe_div(x, y)` has ",
            "`requires!(y != 0)` and a caller passes an unconstrained `y`, the solver can choose ",
            "`y = 0` and reject the call. This is one of the most common verification errors ",
            "because contracts move obligations from the function body to its callers.",
        ),
        suggestion: concat!(
            "Prove the callee's requirement right before the call, usually with a guard like ",
            "`if y == 0 { ... } else { safe_div(x, y) }` or an assertion justified by earlier ",
            "facts. If every caller struggles with the same requirement, reconsider the API and ",
            "weaken the callee contract or move the check inside the function.",
        ),
    },
    ErrorEntry {
        code: "E009",
        short: "Postcondition failed",
        explanation: concat!(
            "A postcondition is what the function promises to every caller once the preconditions ",
            "hold. This error means TrustVc found a return path whose result or final state does ",
            "not satisfy an `ensures!` clause. For example, `ensures!(result >= x)` fails for ",
            "`fn dec(x: i32) -> i32 { x - 1 }`, because the solver can choose any `x` and show ",
            "the returned value is smaller. In short, the specification is stronger than the ",
            "implementation you currently have.",
        ),
        suggestion: concat!(
            "Either change the code so every exit really produces the promised fact, or weaken ",
            "the contract to match the behavior you intend to support. Useful patterns are ",
            "returning `x` or `max(x, 0)` instead of `x - 1`, or changing `ensures!(result >= x)` ",
            "to something the implementation can prove, such as `ensures!(result + 1 == x)`.",
        ),
    },
    ErrorEntry {
        code: "E010",
        short: "Unreachable proof obligation failed",
        explanation: concat!(
            "An `unreachable` or contradiction-style proof obligation means you are claiming that ",
            "no verified execution can ever arrive at that point. This error means the solver ",
            "still found a legal path into the supposedly impossible branch. For example, ",
            "`if x < 10 { ... } else if x > 20 { ... } else { unreachable!() }` is wrong because ",
            "values like `x = 15` still reach the last branch. In verification terms, you have ",
            "not yet proved the contradiction that would make the branch impossible.",
        ),
        suggestion: concat!(
            "Make the case split exhaustive, or prove the missing fact before the unreachable ",
            "point with an assertion or stronger precondition. A common repair is to replace the ",
            "impossible branch with real handling for the uncovered values, or add something like ",
            "`requires!(x < 10 || x > 20)` if that truly is guaranteed by callers.",
        ),
    },
    ErrorEntry {
        code: "E011",
        short: "Type mismatch",
        explanation: concat!(
            "The verifier needs both sides of an expression to have compatible logical types, ",
            "just as Rust needs compatible runtime types. This error means a proof mixed things ",
            "like `u8` and `u32`, signed and unsigned integers, or collections with different ",
            "element types in one obligation. For example, `ensures!(result == x + y)` is ",
            "ambiguous if `x: u8`, `y: u32`, and the proof never states how `x` should be ",
            "widened. New users often hit this with literals too, such as comparing a `usize` ",
            "length against plain `0` or `-1` without making the type explicit.",
        ),
        suggestion: concat!(
            "Convert values at the boundary and keep the proof in one type, for example ",
            "`let x32 = x as u32; ensures!(result == x32 + y)`. Typed literals like `0usize`, ",
            "`0u32`, and explicit helper variables usually make obligations easier for both ",
            "Rust and TrustVc to understand.",
        ),
    },
    ErrorEntry {
        code: "E012",
        short: "Unknown function",
        explanation: concat!(
            "This error means the verifier tried to reason about a function symbol that does not ",
            "exist in the current verification context. The Rust code may compile, but TrustVc ",
            "still needs a logical description of the function before it can use it in proofs. ",
            "For example, calling an external function like `extern \"C\" fn magic(x: i32) -> i32;` ",
            "inside a verified postcondition can trigger this if no spec or verified wrapper ",
            "tells TrustVc what `magic` means. The same thing can happen when a helper function ",
            "is out of scope for verification or was not lowered into the proof environment.",
        ),
        suggestion: concat!(
            "Bring the function into the verification world explicitly: import the right module, ",
            "add the missing spec or extern declaration, or wrap the call in a small verified ",
            "helper whose behavior you can state. If the function is not meant to be reasoned ",
            "about directly, hide it behind an interface with a clear contract and prove callers ",
            "against that contract instead of the raw symbol.",
        ),
    },
    ErrorEntry {
        code: "E013",
        short: "Trigger inference failed",
        explanation: concat!(
            "Quantified formulas like 'for all indices' are not applied magically; SMT solvers ",
            "need a trigger, which is a pattern telling them when to use the quantified fact. ",
            "This error means TrustVc could not infer a sound and useful trigger from the formula ",
            "you wrote. For example, a statement like `forall i. 0 <= i && i < n ==> i + 1 > i` ",
            "contains only arithmetic terms, so the solver has no stable application like ",
            "`xs[i]` or `map.lookup(i)` to trigger on. When trigger inference fails, the proof ",
            "may either never use the quantifier or use it in an unstable way.",
        ),
        suggestion: concat!(
            "Rewrite the quantified fact around a stable term the solver will actually see, such ",
            "as `xs[i]`, `set.contains(i)`, or `map.lookup(i)`, and add an explicit trigger if ",
            "TrustVc supports it. Another effective pattern is to split one broad `forall` into ",
            "smaller lemmas so each lemma mentions the concrete term later assertions will use.",
        ),
    },
    ErrorEntry {
        code: "E014",
        short: "Quantifier instantiation limit reached",
        explanation: concat!(
            "This error means the solver started instantiating a quantified fact repeatedly and ",
            "hit its internal limit before finishing the proof search. The proof is not ",
            "necessarily false; it may just be too large or too self-referential for the current ",
            "encoding. For example, a property like `forall i, j. 0 <= i && i < j && j < n ==> ",
            "xs[i] <= xs[j]` can generate many combinations of `i` and `j`, especially when it ",
            "is mixed with other quantified lemmas. New users often see this when a single giant ",
            "quantified statement is asked to do the work of several smaller facts.",
        ),
        suggestion: concat!(
            "Reduce the search space by splitting the statement into smaller lemmas, bounding the ",
            "quantified range more tightly, or improving trigger terms so the solver instantiates ",
            "only when needed. A practical repair is to prove a local fact like `xs[k] <= xs[k + ",
            "1]` first and use a separate lemma for transitive reasoning instead of one ",
            "monolithic `forall`.",
        ),
    },
    ErrorEntry {
        code: "E015",
        short: "Solver timeout",
        explanation: concat!(
            "A solver timeout means TrustVc ran out of time before it could prove or refute the ",
            "obligation. This is different from a counterexample: the tool is saying 'I do not ",
            "know yet,' not 'your property is false.' For example, a proof that combines ",
            "recursive specs, several `forall` clauses, and nonlinear arithmetic may be valid but ",
            "still overwhelm the solver. In practice, timeouts usually mean the proof needs to be ",
            "broken into smaller, more explicit steps.",
        ),
        suggestion: concat!(
            "Simplify the obligation before increasing limits: add helper lemmas, assert ",
            "intermediate facts near the code that creates them, and isolate expensive arithmetic ",
            "or quantifier reasoning into smaller units. Only after the structure is reasonable ",
            "should you raise the timeout, because a slower version of the same tangled proof is ",
            "usually not the best fix.",
        ),
    },
    ErrorEntry {
        code: "E016",
        short: "Encoding error",
        explanation: concat!(
            "An encoding error means TrustVc failed while translating your verified Rust program ",
            "into solver input. Unlike `Assertion failed`, this usually points to a tool ",
            "limitation or internal bug rather than a false program property. For example, a ",
            "dense expression that mixes pattern matching, recursive specs, and quantified terms ",
            "in one obligation can expose an encoding path that TrustVc does not yet handle ",
            "correctly. When you see this error, the best first move is to isolate the smallest ",
            "expression or construct that still triggers it.",
        ),
        suggestion: concat!(
            "Refactor the failing obligation into smaller helper functions or lemmas so you can ",
            "identify the exact construct that breaks translation. Replacing a dense one-liner ",
            "with named intermediate values often exposes the trigger, and the minimized example ",
            "is exactly what you need for a reliable workaround or a targeted bug fix.",
        ),
    },
    ErrorEntry {
        code: "E017",
        short: "Unsupported operation",
        explanation: concat!(
            "This error means the source program uses a language feature or proof construct that ",
            "the current TrustVc backend does not model yet. In other words, the verifier ",
            "understands your goal in principle, but it does not know how to reason about this ",
            "specific kind of operation. For example, trying to verify properties of floating-",
            "point arithmetic, raw pointer arithmetic, or another backend-specific feature may ",
            "trigger this when no logical model exists for it. The code may be valid Rust, but ",
            "the verifier cannot currently talk about it.",
        ),
        suggestion: concat!(
            "Move the unsupported code behind a small trusted boundary and verify the surrounding ",
            "logic against a clean contract. When possible, rewrite the proof in terms of ",
            "supported model types like integers, slices, or pure helper functions, or add the ",
            "missing lowering and encoding support if you are extending TrustVc itself.",
        ),
    },
    ErrorEntry {
        code: "E018",
        short: "Assertion-by contradiction failed",
        explanation: concat!(
            "An assertion-by-contradiction proof works by assuming the negation of your goal and ",
            "then deriving an impossible fact. This error means the proof block never actually ",
            "reached that contradiction. For example, `assert!(x < y) by { assume!(x >= y); }` is ",
            "not enough on its own, because the proof still needs facts that connect `x` and `y` ",
            "to something impossible. Usually the high-level idea is right, but one or two bridge ",
            "steps are missing.",
        ),
        suggestion: concat!(
            "Inside the proof block, derive the missing intermediate facts step by step instead ",
            "of jumping straight from the negated goal to `false`. Good patterns are asserting ",
            "smaller arithmetic consequences, calling a lemma that connects your assumptions, or ",
            "splitting one big contradiction proof into two shorter `assert!` statements.",
        ),
    },
    ErrorEntry {
        code: "E019",
        short: "Broadcast cap hit",
        explanation: concat!(
            "Broadcast lemmas are facts that TrustVc automatically injects into the proof context ",
            "in many places. This error means that expansion grew too large and hit the ",
            "configured cap before all requested facts were imported. For example, if several ",
            "powerful collection lemmas are marked for broadcast and each proof step pulls all of ",
            "them in, the context can balloon long before the solver reaches the line you care ",
            "about. New users often read this as 'the proof needs more facts,' but the real issue ",
            "is usually that too many broad facts are being loaded at once.",
        ),
        suggestion: concat!(
            "Prefer targeted proof steps over global broadcast when possible: call the one lemma ",
            "you need, reveal a specific definition, or narrow the scope so unrelated facts stay ",
            "out of the context. Increase the cap only after trimming the broadcast set, because ",
            "more automatic facts often make proofs slower and less predictable rather than ",
            "better.",
        ),
    },
    ErrorEntry {
        code: "E020",
        short: "Fuel exhausted",
        explanation: concat!(
            "Fuel is the budget TrustVc uses for unfolding recursive definitions during a proof. ",
            "This error means the solver stopped expanding a recursive function or predicate ",
            "before it had enough detail to finish the argument. For example, if `spec fn sum(xs)` ",
            "unfolds one element at a time, proving something about `sum([1, 2, 3])` may require ",
            "more unfolding than the default fuel allows. The function is not necessarily wrong; ",
            "the proof just cannot see far enough into its definition yet.",
        ),
        suggestion: concat!(
            "Reveal or unfold the specific recursive definition at the point where you need it, ",
            "or prove a helper lemma that exposes exactly one step of the recursion. Another good ",
            "pattern is reasoning on smaller inputs like `&xs[1..]` and using an inductive lemma, ",
            "instead of depending on the solver to unfold many recursive calls automatically.",
        ),
    },
    ErrorEntry {
        code: "E021",
        short: "Model validation failed",
        explanation: concat!(
            "A model validation failure means the solver produced a candidate counterexample, but ",
            "TrustVc could not confirm that the model is internally consistent with the obligation ",
            "it sent. This is not the same as a normal proof failure, because the reported ",
            "counterexample may be incomplete, malformed, or based on a solver behavior TrustVc ",
            "does not fully support. For example, a proof involving quantified map properties ",
            "like `forall k. map.lookup(k) == 0` can yield a model for `lookup` that looks ",
            "acceptable to the solver but fails TrustVc's own checks. Treat this as a diagnostic ",
            "about the toolchain first, not as immediate evidence that your program is wrong.",
        ),
        suggestion: concat!(
            "Minimize the failing proof to the smallest example that still produces the validation ",
            "error and inspect the reported bindings for the construct involved. Simplifying ",
            "quantifiers or recursive specs around the failing obligation can provide a temporary ",
            "workaround, but the durable fix is usually a small reproducer and a targeted TrustVc ",
            "bug fix.",
        ),
    },
];

/// Returns the catalog entry for the given error code, or `None` if unknown.
pub fn lookup(code: &str) -> Option<&'static ErrorEntry> {
    CATALOG.iter().find(|entry| entry.code == code)
}

/// Format a full diagnostic message for a given error code, suitable for terminal display.
///
/// Returns a multi-line string like:
///
/// ```text
/// error[E001]: Assertion failed
///
///   In formal verification...
///
///   Suggestion: Either strengthen...
/// ```
pub fn format_diagnostic(code: &str) -> Option<String> {
    let entry = lookup(code)?;
    let mut msg = String::new();
    use std::fmt::Write;

    let _ = writeln!(msg, "error[{}]: {}", entry.code, entry.short);
    let _ = writeln!(msg);
    for line in entry.explanation.lines() {
        let _ = writeln!(msg, "  {}", line);
    }
    let _ = writeln!(msg);
    let _ = writeln!(msg, "  Suggestion: {}", entry.suggestion);
    Some(msg)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lookup_known_code() {
        let entry = lookup("E001").unwrap();
        assert_eq!(entry.short, "Assertion failed");
    }

    #[test]
    fn test_lookup_unknown_code() {
        assert!(lookup("E999").is_none());
    }

    #[test]
    fn test_format_diagnostic_contains_title_and_suggestion() {
        let diag = format_diagnostic("E001").unwrap();
        assert!(diag.contains("Assertion failed"));
        assert!(diag.contains("Suggestion:"));
    }

    #[test]
    fn test_all_codes_have_nonempty_fields() {
        for entry in CATALOG {
            assert!(!entry.code.is_empty());
            assert!(!entry.short.is_empty());
            assert!(!entry.explanation.is_empty());
            assert!(!entry.suggestion.is_empty());
        }
    }
}
