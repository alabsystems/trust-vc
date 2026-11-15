// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS-CRITICAL. The proof-block mode discipline, enforced at the
//! LOWERING SEAM rather than by a token scanner.
//!
//! `trust_vc::proof_block!` expands, in any build without `cfg(trust_mc)`, to
//! `let _ = || { ..body.. };` — a closure that is never called. Every write it
//! performs to an EXEC binding is therefore erased by the compiler while the
//! body model propagates it into the surrounding solver state. Believing one is
//! a false `Verified`, and it was measured: `proof_block!({ e = 7 })` verified
//! `e == 7` while the compiled program left `e == 0`, and the liar twin
//! `assert!(e == 0)` came back `Counterexample`.
//!
//! A first fix put the rule in `mode_body`, which scans TOKENS, and a token
//! scanner cannot decide the question — it is guessing at what PLACE a
//! statement writes. Three witnesses walked straight through it, and a fourth
//! honest pattern was wrongly rejected. Each has a test below:
//!
//! | witness | what the token pass did |
//! |---|---|
//! | `s.g = 7` with a `let g` in the block | keyed the write on the FIELD ident `g` |
//! | `v[0] = 7` | wanted an `Ident` before `=`, found a bracket `Group`, saw no write |
//! | `e >>= 3` | two-character compound table; the leading `>` was unrecognized |
//! | `trust_vc_proof_block!` | the engine dispatches the alias; the token pass did not |
//! | `flag && cond` | read the Joint `&` as a compound assignment to `flag` |
//! | `let e = j;` after `let ghost j` | `let ghost` parsed, but only for the token pass |
//!
//! The first three are ONE defect wearing three hats. They are now decided by
//! `field_index_projection_root` — the same place-root resolver the `&mut`
//! referent analysis uses — inside `check_proof_block_place_writes`, so no
//! spelling can defeat them. The NON-VACUITY controls at the bottom are what
//! keep the gate from degenerating into "reject every proof block".

use std::io::Write;
use trust_vc_core::{verify_function_from_file, VerifyResult};

const SRC: &str = r####"
struct S { g: u64 }
struct Wrap { v: Vec<u64> }

// ===== witness 1: NAME COLLISION ON A FIELD WRITE =====
// `let g` inside the block is a proof-local; `s.g` is a field of the EXEC local
// `s`. Keying on the last ident before `=` conflated them.
fn w1_field_shadow_bypass() {
    let mut s: S = S { g: 0u64 };
    trust_vc::proof_block!({
        let g: u64 = 1u64;
        s.g = 7u64;
    });
    trust_vc::assert!(s.g == 7u64);
}

// The liar twin: it came back Counterexample, which proves the solver genuinely
// held `s.g == 7` rather than merely failing to refute it.
fn w1_field_shadow_liar() {
    let mut s: S = S { g: 0u64 };
    trust_vc::proof_block!({
        let g: u64 = 1u64;
        s.g = 0u64;
    });
    trust_vc::assert!(s.g == 7u64);
}

// Deeper projection: no `let` collision at all, just a place the scanner could
// not root.
fn w1_nested_field_write(w: &mut Wrap) {
    trust_vc::proof_block!({
        w.v = Vec::new();
    });
}

// ===== witness 2: INDEX WRITE INVISIBLE =====
fn w2_index_write_liar() {
    let mut v: [u64; 3] = [0u64, 0u64, 0u64];
    trust_vc::proof_block!({
        v[0] = 7u64;
    });
    trust_vc::assert!(v[0] != 0u64);
}

// ===== witness 3: SHIFT-ASSIGNMENT ESCAPES =====
fn w3_shr_assign() {
    let mut e: u64 = 8u64;
    trust_vc::proof_block!({
        e >>= 3u64;
    });
    trust_vc::assert!(e == 1u64);
}

fn w3_shl_assign() {
    let mut e: u64 = 1u64;
    trust_vc::proof_block!({
        e <<= 3u64;
    });
    trust_vc::assert!(e == 8u64);
}

// Every other compound operator, so the class is pinned and not just the two
// spellings the reviewer happened to send.
fn w3_add_assign() {
    let mut e: u64 = 1u64;
    trust_vc::proof_block!({ e += 3u64; });
    trust_vc::assert!(e == 4u64);
}
fn w3_bitor_assign() {
    let mut e: u64 = 1u64;
    trust_vc::proof_block!({ e |= 2u64; });
    trust_vc::assert!(e == 3u64);
}
fn w3_bitand_assign() {
    let mut e: u64 = 3u64;
    trust_vc::proof_block!({ e &= 1u64; });
    trust_vc::assert!(e == 1u64);
}
fn w3_bitxor_assign() {
    let mut e: u64 = 3u64;
    trust_vc::proof_block!({ e ^= 1u64; });
    trust_vc::assert!(e == 2u64);
}
fn w3_rem_assign() {
    let mut e: u64 = 7u64;
    trust_vc::proof_block!({ e %= 4u64; });
    trust_vc::assert!(e == 3u64);
}

// ===== witness 4: THE ENGINE'S OWN ALIAS =====
// `body_extract` dispatches `"proof_block" | "trust_vc_proof_block"`.
fn w4_alias_bypass() {
    let mut e: u64 = 0u64;
    trust_vc::trust_vc_proof_block!({
        e = 7u64;
    });
    trust_vc::assert!(e == 7u64);
}

fn w4_alias_bare() {
    let mut e: u64 = 0u64;
    trust_vc_proof_block!({
        e = 7u64;
    });
    trust_vc::assert!(e == 7u64);
}

// ===== further spellings the place resolver decides by construction =====

fn w5_deref_write(p: &mut u64) {
    trust_vc::proof_block!({
        *p = 7u64;
    });
    trust_vc::assert!(*p == 7u64);
}

fn w5_param_write(a: u64) -> u64 {
    let mut e: u64 = a;
    trust_vc::proof_block!({
        e = 7u64;
    });
    e
}

// Nested block, if-body, loop body — the walk must reach them all.
fn w5_nested_block() {
    let mut e: u64 = 0u64;
    trust_vc::proof_block!({
        {
            e = 7u64;
        }
    });
    trust_vc::assert!(e == 7u64);
}

fn w5_if_body(a: u64) {
    let mut e: u64 = 0u64;
    trust_vc::proof_block!({
        if a > 0u64 {
            e = 7u64;
        }
    });
    trust_vc::assert!(e == 7u64 || e == 0u64);
}

// NESTED proof blocks: `syn::visit` does not enter macro tokens, so the gate
// parses and walks the nest itself.
fn w5_nested_proof_block() {
    let mut e: u64 = 0u64;
    trust_vc::proof_block!({
        trust_vc::proof_block!({
            e = 7u64;
        });
    });
    trust_vc::assert!(e == 7u64);
}

// A MUTATING METHOD is the same erased write wearing a method name.
fn w5_method_mutation(w: &mut Wrap) {
    trust_vc::proof_block!({
        w.v.push(1u64);
    });
}

// Handing an exec place out through `&mut`.
fn w5_mut_borrow_out() {
    let mut e: u64 = 0u64;
    trust_vc::proof_block!({
        let r: &mut u64 = &mut e;
        *r = 7u64;
    });
    trust_vc::assert!(e == 7u64);
}

// ===== witness 6: a `let ghost` local READ BY EXEC CODE =====
// Round 1 taught `let ghost` to parse but only the token pass understood it:
// the encoder still modelled `j` as an ordinary local, so exec code reading it
// received the ghost value while the compiler erases the binding entirely.
fn w6_ghost_read_by_exec() {
    let ghost mut j: u64 = 3u64;
    trust_vc::proof_block!({
        j = 9u64;
    });
    let e: u64 = j;
    trust_vc::assert!(e == 9u64);
}

fn w6_ghost_read_in_exec_assignment(a: u64) {
    let ghost g: u64 = a;
    let mut e: u64 = 0u64;
    e = g;
    trust_vc::assert!(e == a);
}

fn w6_tracked_read_by_exec(a: u64) {
    let tracked t: u64 = a;
    let e: u64 = t + 1u64;
    trust_vc::assert!(e == a + 1u64);
}

fn w6_ghost_read_in_exec_call_arg(a: u64) -> u64 {
    let ghost g: u64 = a;
    exec_identity(g)
}

fn exec_identity(x: u64) -> u64 {
    x
}

fn w6_ghost_read_in_exec_condition(a: u64) -> u64 {
    let ghost g: bool = a > 0u64;
    if g {
        1u64
    } else {
        0u64
    }
}

// ===== NON-VACUITY: honest programs that must STILL verify =====

// Finding 5: `&&` / `||` inside a proof block. The first `&` of `&&` and the
// first `|` of `||` are `Spacing::Joint`, so a predicate that accepted any
// Joint punct in its compound table read `flag &&` as an assignment to `flag`
// — and an unmodelled name defaults to exec, so the block was REJECTED. The
// pattern is everywhere.
fn ok_andand(a: u64) {
    let flag: bool = a > 0u64;
    trust_vc::proof_block!({
        if flag && a > 0u64 {
            trust_vc::assert!(a > 0u64);
        }
    });
}

fn ok_oror(a: u64) {
    let flag: bool = a > 0u64;
    trust_vc::proof_block!({
        if flag || a == 0u64 {
            trust_vc::assert!(true);
        }
    });
}

// The localizing control: the SAME `&&` in plain exec code.
fn ok_andand_in_exec(a: u64) {
    let flag: bool = a > 0u64;
    if flag && a > 0u64 {
        trust_vc::assert!(a > 0u64);
    }
}

// Every non-assignment operator whose leading punct is Joint.
fn ok_joint_puncts_are_not_assignments(a: u64) {
    let x: u64 = a;
    trust_vc::proof_block!({
        let _s: u64 = x << 1u64;
        let _t: u64 = x >> 1u64;
        let _u: u64 = x & 1u64;
        let _v: u64 = x | 1u64;
        let _w: bool = x == a;
        let _y: bool = x != a;
        let _z: bool = x <= a;
        let _q: bool = x >= a;
        trust_vc::assert!(_w);
    });
}

// A ghost local written from a proof block: the accept side of the gate.
fn ok_ghost_write(a: u64) {
    let ghost mut j: u64 = a;
    trust_vc::proof_block!({
        j = add(j, 2u64);
    });
    trust_vc::assert!(j == add(a, 2u64));
}

// A `Ghost<T>`-DECLARED local is ghost mode too, without the `let ghost` sugar.
#[trust_vc::requires(a < 10u64)]
fn ok_ghost_typed_write(a: u64) {
    let mut j: Ghost<u64> = Ghost(a);
    trust_vc::proof_block!({
        j = Ghost(a);
    });
    trust_vc::assert!(a < 10u64);
}

// A block-LOCAL binding of the proof block, written there: the block owns it.
fn ok_proof_local_write() {
    trust_vc::proof_block!({
        let mut t: u64 = 1u64;
        t = 2u64;
        t += 1u64;
        trust_vc::assert!(t == 3u64);
    });
}

// READING an exec local in a proof block is legal — only WRITING is erased.
fn ok_proof_reads_exec(a: u64) {
    let e: u64 = a;
    trust_vc::proof_block!({
        trust_vc::assert!(e == a);
    });
}

// A PURE method on an exec local inside a proof block.
fn ok_pure_method_on_exec(w: &Wrap) {
    trust_vc::proof_block!({
        let _n: usize = w.v.len();
        trust_vc::assert!(true);
    });
}

// A ghost local read by SPEC code (an assert / an ensures) is the whole point
// of having one.
#[trust_vc::ensures(true)]
fn ok_ghost_read_by_spec(a: u64) {
    let ghost g: u64 = a;
    trust_vc::assert!(g == a);
}

// An EXEC local SHADOWING a ghost name is exec again: writing it from a proof
// block must be REJECTED even though the ghost name is still in an outer scope.
fn shadow_exec_over_ghost(a: u64) {
    let ghost mut j: u64 = a;
    trust_vc::assert!(j == a);
    {
        let mut j: u64 = 0u64;
        trust_vc::proof_block!({
            j = 7u64;
        });
        trust_vc::assert!(j == 7u64);
    }
}

// ... and the twin: a GHOST local shadowing an exec name is writable.
fn shadow_ghost_over_exec(a: u64) {
    let mut j: u64 = 0u64;
    j = a;
    {
        let ghost mut j: u64 = a;
        trust_vc::proof_block!({
            j = add(j, 2u64);
        });
        trust_vc::assert!(j == add(a, 2u64));
    }
}

// ===== pattern binders: a match arm / closure param / `for` / `if let` binds
// names WITHOUT a `let` statement. The block owns them, so writing one is legal
// — but the binding must stay scoped to the construct that introduced it. =====

fn ok_closure_param_write() {
    trust_vc::proof_block!({
        let f = |mut x: u64| {
            x = 1u64;
            x
        };
        trust_vc::assert!(true);
    });
}

fn ok_match_arm_binding(a: u64) {
    trust_vc::proof_block!({
        match a {
            mut y => {
                y = 1u64;
            }
        }
        trust_vc::assert!(true);
    });
}

fn ok_if_let_binding(o: Option<u64>) {
    trust_vc::proof_block!({
        if let Some(mut y) = o {
            y = 1u64;
        }
        trust_vc::assert!(true);
    });
}

// ... and the SCOPING twin, which is a soundness matter, not a convenience one:
// `if let Some(y) = o { .. } else { .. }` does NOT bind `y` in the `else`, so a
// write to the OUTER exec `y` there must still be rejected.
fn if_let_binding_does_not_leak_into_else(o: Option<u64>) {
    let mut y: u64 = 0u64;
    trust_vc::proof_block!({
        if let Some(_v) = o {
            trust_vc::assert!(true);
        } else {
            y = 7u64;
        }
    });
    trust_vc::assert!(y == 7u64);
}

// A closure inside a proof block writing an OUTER exec local is still erased.
fn closure_writing_outer_exec_local_is_rejected() {
    let mut e: u64 = 0u64;
    trust_vc::proof_block!({
        let f = || {
            e = 7u64;
        };
        f();
    });
    trust_vc::assert!(e == 7u64);
}

// The SIBLING proof-block lowering: `assert_by!`'s block is visited under a
// scope SNAPSHOT that is restored afterwards (`extract_scoped_proof_block`), so
// a write inside it never reaches the surrounding state. This is the structural
// reason it is not a fourth spelling of the same hole — pinned so a future
// change to that lowering cannot quietly open one.
fn assert_by_block_write_does_not_propagate(a: u64) {
    let mut e: u64 = 0u64;
    trust_vc::assert_by!(a == a, {
        e = 7u64;
    });
    trust_vc::assert!(e == 7u64);
}

// A local actually NAMED `ghost` is not a mode marker.
fn ok_local_named_ghost() {
    let mut ghost: u64 = 5u64;
    ghost = 6u64;
    trust_vc::assert!(ghost == 6u64);
}

// ===== ROUND 3, witness 7: A FUNCTION-LOCAL `macro_rules!` =====
// `syn::visit` does not descend into a macro's token stream, but `body_extract`
// EXPANDS single-arm zero-argument function-local macros and lowers what they
// expand to. So the gate saw nothing while the engine believed the write, and
// all three round-1 witnesses reappeared VERBATIM inside one. The gate now walks
// the same expansion the collector will.
fn w7_macro_plain_write() {
    let mut e: u64 = 0u64;
    macro_rules! wr {
        () => {
            e = 7u64;
        };
    }
    trust_vc::proof_block!({
        wr!();
    });
    trust_vc::assert!(e == 7u64);
}

// The liar twin: the macro writes 0 and the assertion claims 7. It came back
// Counterexample, so the solver genuinely held the erased value.
fn w7_macro_plain_write_liar() {
    let mut e: u64 = 0u64;
    macro_rules! wr {
        () => {
            e = 0u64;
        };
    }
    trust_vc::proof_block!({
        wr!();
    });
    trust_vc::assert!(e == 7u64);
}

fn w7_macro_field_write() {
    let mut s: S = S { g: 0u64 };
    macro_rules! wr {
        () => {
            s.g = 7u64;
        };
    }
    trust_vc::proof_block!({
        wr!();
    });
    trust_vc::assert!(s.g == 7u64);
}

fn w7_macro_compound_write() {
    let mut e: u64 = 8u64;
    macro_rules! wr {
        () => {
            e >>= 3u64;
        };
    }
    trust_vc::proof_block!({
        wr!();
    });
    trust_vc::assert!(e == 1u64);
}

// Declared INSIDE the proof block, so the gate must register the item during its
// own walk rather than inheriting it from the collector's scopes.
fn w7_macro_declared_inside_block() {
    let mut e: u64 = 0u64;
    trust_vc::proof_block!({
        macro_rules! wr {
            () => {
                e = 7u64;
            };
        }
        wr!();
    });
    trust_vc::assert!(e == 7u64);
}

fn w7_macro_through_the_alias() {
    let mut e: u64 = 0u64;
    macro_rules! wr {
        () => {
            e = 7u64;
        };
    }
    trust_vc::trust_vc_proof_block!({
        wr!();
    });
    trust_vc::assert!(e == 7u64);
}

// A macro whose expansion writes only a binding the BLOCK owns is honest, and a
// local macro must not become a blanket refusal.
fn ok_macro_writes_a_proof_local() {
    trust_vc::proof_block!({
        let mut y: u64 = 0u64;
        macro_rules! wr {
            () => {
                y = 7u64;
            };
        }
        wr!();
        trust_vc::assert!(y == 7u64);
    });
}

// The plain-EXEC control: the same macro writing the same local outside a proof
// block is an ordinary write and must still verify. This localizes the fault to
// the proof-block path.
fn ok_macro_in_exec_code() {
    let mut e: u64 = 0u64;
    macro_rules! wr {
        () => {
            e = 7u64;
        };
    }
    wr!();
    trust_vc::assert!(e == 7u64);
}

// ===== ROUND 3, witness 8: PURE SPEC COMBINATORS ARE NOT WRITES =====
// `Seq::push`, `Seq::update`, `Set::insert`/`remove` and `Map::insert`/`remove`
// RETURN A NEW VALUE and mutate nothing — they are the standard way to build a
// ghost collection in a proof. Their names collide with `Vec`/`HashSet`/
// `HashMap` in-place mutators, so a method-NAME blacklist refused all six.
fn ok_seq_push(s: Seq<u64>) {
    trust_vc::proof_block!({
        let _t = s.push(1u64);
        trust_vc::assert!(true);
    });
}

fn ok_seq_update(s: Seq<u64>) {
    trust_vc::proof_block!({
        let _t = s.update(0, 1u64);
        trust_vc::assert!(true);
    });
}

fn ok_set_insert(s: Set<u64>) {
    trust_vc::proof_block!({
        let _t = s.insert(1u64);
        trust_vc::assert!(true);
    });
}

fn ok_set_remove(s: Set<u64>) {
    trust_vc::proof_block!({
        let _t = s.remove(1u64);
        trust_vc::assert!(true);
    });
}

fn ok_map_insert(m: Map<u64, u64>) {
    trust_vc::proof_block!({
        let _t = m.insert(1u64, 2u64);
        trust_vc::assert!(true);
    });
}

fn ok_map_remove(m: Map<u64, u64>) {
    trust_vc::proof_block!({
        let _t = m.remove(1u64);
        trust_vc::assert!(true);
    });
}

// NON-VACUITY for the relaxation above: the SAME method name on an EXEC
// container is still a write. `Vec` and `Seq` both lower to `TrustVcType::Seq`,
// so this is decided by the declaration's `bounded_len` provenance bit, not by
// the modelled type.
fn w8_vec_push_on_an_exec_param(v: &mut Vec<u64>) {
    trust_vc::proof_block!({
        v.push(1u64);
    });
}

fn w8_vec_push_on_an_exec_local() {
    let mut v: Vec<u64> = Vec::new();
    trust_vc::proof_block!({
        v.push(1u64);
    });
    trust_vc::assert!(v.len() == 1usize);
}

// ===== ROUND 3, witness 9: A GHOST VALUE INSIDE AN EXEC WRITE'S PLACE =====
// `mode_body` rule 1 owns the assigned NAME; it never looked inside the place.
// An index computed from a `let ghost` binding is read by exec code, is erased,
// and the solver believed the resulting write. The tell was that the COMPOUND
// twin was caught while `=` escaped.
fn w9_ghost_index_in_an_exec_write() {
    let ghost i: usize = 1usize;
    let mut v: [u64; 3] = [0u64, 0u64, 0u64];
    v[i] = 7u64;
    trust_vc::assert!(v[1] == 7u64);
}

fn w9_ghost_index_in_an_exec_write_liar() {
    let ghost i: usize = 1usize;
    let mut v: [u64; 3] = [0u64, 0u64, 0u64];
    v[i] = 7u64;
    trust_vc::assert!(v[1] == 0u64);
}

fn w9_ghost_index_compound_twin() {
    let ghost i: usize = 1usize;
    let mut v: [u64; 3] = [0u64, 0u64, 0u64];
    v[i] += 7u64;
    trust_vc::assert!(v[1] == 7u64);
}

// The honest control: the same program with an EXEC index still verifies.
fn ok_exec_index_in_an_exec_write() {
    let i: usize = 1usize;
    let mut v: [u64; 3] = [0u64, 0u64, 0u64];
    v[i] = 7u64;
    trust_vc::assert!(v[1] == 7u64);
}

// ===== ROUND 3, witness 10: A GHOST READ HIDDEN IN A LOCAL MACRO =====
// Same root cause as witness 7, on the READ gate. The whitelist argument for the
// ghost walk was that spec constructs are skipped STRUCTURALLY rather than by a
// macro-name list; the structure also hid exec code.
fn w10_ghost_read_in_a_macro() {
    let ghost j: u64 = 3u64;
    let mut e: u64 = 0u64;
    macro_rules! rd {
        () => {
            e = j;
        };
    }
    rd!();
    trust_vc::assert!(e == 3u64);
}

fn w10_ghost_read_in_a_macro_liar() {
    let ghost j: u64 = 3u64;
    let mut e: u64 = 0u64;
    macro_rules! rd {
        () => {
            e = j;
        };
    }
    rd!();
    trust_vc::assert!(e == 4u64);
}

fn ok_exec_read_in_a_macro() {
    let j: u64 = 3u64;
    let mut e: u64 = 0u64;
    macro_rules! rd {
        () => {
            e = j;
        };
    }
    rd!();
    trust_vc::assert!(e == 3u64);
}

// ===== ROUND 3, witness 11: AN EXEC WRITE TO A GHOST PLACE =====
// Rule 1 catches the bare NAME and misses every projection of it, exactly the
// way the round-1 token pass missed `s.g` and `v[0]`.
fn w11_exec_writes_a_ghost_field() {
    let ghost mut s: S = S { g: 0u64 };
    s.g = 7u64;
    trust_vc::assert!(s.g == 7u64);
}

fn w11_exec_writes_a_ghost_index() {
    let ghost mut v: [u64; 3] = [0u64, 0u64, 0u64];
    v[0] = 7u64;
    trust_vc::assert!(v[0] == 7u64);
}

// The bare NAME, which rule 1 already owned — kept so the two spellings are
// pinned side by side and the division of labour stays visible.
fn w11_exec_writes_a_ghost_name() {
    let ghost mut e: u64 = 0u64;
    e = 7u64;
    trust_vc::assert!(e == 7u64);
}

// A ghost place written from PROOF mode is the whole point of having one.
fn ok_proof_block_writes_a_ghost_field() {
    let ghost mut s: S = S { g: 0u64 };
    trust_vc::proof_block!({
        s.g = 7u64;
        trust_vc::assert!(s.g == 7u64);
    });
}

// A ghost PLACE written from inside a local macro, and a ghost read in an
// EXPRESSION-position macro: the two remaining routes through an expansion.
fn w11_exec_writes_a_ghost_field_in_a_macro() {
    let ghost mut s: S = S { g: 0u64 };
    macro_rules! wr {
        () => {
            s.g = 7u64;
        };
    }
    wr!();
    trust_vc::assert!(s.g == 7u64);
}

fn w10_ghost_read_in_an_expression_macro() {
    let ghost j: u64 = 3u64;
    macro_rules! rd {
        () => {
            j
        };
    }
    let e: u64 = rd!();
    trust_vc::assert!(e == 3u64);
}

// A macro that expands TO a proof block, a macro invoked inside a NESTED proof
// block, and a macro that DEFINES a macro: three more ways to put a statement
// behind an expansion.
fn w7_macro_expands_to_a_proof_block() {
    let mut e: u64 = 0u64;
    macro_rules! pb {
        () => {
            trust_vc::proof_block!({
                e = 7u64;
            });
        };
    }
    pb!();
    trust_vc::assert!(e == 7u64);
}

fn w7_macro_inside_a_nested_proof_block() {
    let mut e: u64 = 0u64;
    macro_rules! wr {
        () => {
            e = 7u64;
        };
    }
    trust_vc::proof_block!({
        trust_vc::proof_block!({
            wr!();
        });
    });
    trust_vc::assert!(e == 7u64);
}

fn w7_macro_defines_a_macro() {
    let mut e: u64 = 0u64;
    macro_rules! outer {
        () => {
            macro_rules! inner {
                () => {
                    e = 7u64;
                };
            }
            inner!();
        };
    }
    trust_vc::proof_block!({
        outer!();
    });
    trust_vc::assert!(e == 7u64);
}

// A write laundered through a `&mut` borrow of a FIELD, and one in a LOOP body.
fn w7_mut_borrow_of_a_field() {
    let mut s: S = S { g: 0u64 };
    trust_vc::proof_block!({
        let r: &mut u64 = &mut s.g;
        *r = 7u64;
    });
    trust_vc::assert!(s.g == 7u64);
}

fn w7_write_in_a_loop_body() {
    let mut e: u64 = 0u64;
    trust_vc::proof_block!({
        let mut i: u64 = 0u64;
        while i < 1u64 {
            e = 7u64;
            i = i + 1u64;
        }
    });
    trust_vc::assert!(e == 7u64);
}

// OVER-REJECTION controls for the fail-closed macro rule: every spec lane the
// engine gives a name-keyed meaning to must still be walked past.
fn ok_spec_macros_inside_a_proof_block(a: u64) {
    trust_vc::proof_block!({
        trust_vc::assert_by!(a == a, {
            trust_vc::assert!(true);
        });
        trust_vc::assert!(1u64 + 1u64 == 2u64);
    });
}

fn ok_assume_inside_a_proof_block(a: u64) {
    trust_vc::proof_block!({
        trust_vc::assume!(a > 0u64);
    });
    trust_vc::assert!(a > 0u64);
}

// A local `macro_rules!` that SHADOWS a spec-lane name. `macro_scope` renames it
// to the quarantine name, and the gate then refuses it fail-closed rather than
// skipping it as the spec macro it is impersonating.
fn w7_shadowed_spec_macro_name_writes_exec() {
    let mut e: u64 = 0u64;
    macro_rules! seq {
        () => {
            e = 7u64;
        };
    }
    trust_vc::proof_block!({
        seq!();
    });
    trust_vc::assert!(e == 7u64);
}

fn ok_seq_macro_inside_a_proof_block() {
    trust_vc::proof_block!({
        let s: Seq<u64> = trust_vc_types::seq![1u64, 2u64];
        trust_vc::assert!(s.len() == 2);
    });
}

// ===== ROUND 4, witness 12: A PLACE WHOSE ROOT THE RESOLVER CANNOT REACH =====
// `check_place`'s `None` arm was the one disposition of the gate with no named
// test behind it: neutralizing it to fail-open broke nothing. A DESTRUCTURING
// assignment reaches it — `(e, f) = ..` is an `Expr::Assign` whose LHS is an
// `Expr::Tuple`, which `field_index_projection_root` cannot reduce to a root
// identifier at all — and it writes TWO exec locals at once.
fn w12_tuple_destructure_assign() {
    let mut e: u64 = 0u64;
    let mut f: u64 = 0u64;
    trust_vc::proof_block!({
        (e, f) = (7u64, 8u64);
    });
    trust_vc::assert!(e == 7u64);
}

fn w12_slice_destructure_assign() {
    let mut e: u64 = 0u64;
    let mut f: u64 = 0u64;
    trust_vc::proof_block!({
        [e, f] = [7u64, 8u64];
    });
    trust_vc::assert!(e == 7u64);
}

fn w12_struct_destructure_assign() {
    let mut e: u64 = 0u64;
    trust_vc::proof_block!({
        S { g: e } = S { g: 7u64 };
    });
    trust_vc::assert!(e == 7u64);
}

// The COMPOUND-assignment route into the same arm, so both `check_place`
// callers are covered rather than only `Expr::Assign`. A deref of a CALL is a
// place with no root identifier: `field_index_projection_root` peels the `*`
// and then meets an `Expr::Call`, which it cannot follow.
fn exec_slot(v: &mut Vec<u64>) -> &mut u64 {
    &mut v[0]
}

fn w12_unresolved_place_compound_assign(v: &mut Vec<u64>) {
    trust_vc::proof_block!({
        *exec_slot(v) += 7u64;
    });
    trust_vc::assert!(v[0] == 7u64);
}

fn w12_unresolved_place_plain_assign(v: &mut Vec<u64>) {
    trust_vc::proof_block!({
        *exec_slot(v) = 7u64;
    });
    trust_vc::assert!(v[0] == 7u64);
}

// ===== ROUND 4, item 3: A `&mut` VIEW OF AN EXEC CONTAINER =====
// INTENDED BEHAVIOUR, pinned so it is not mistaken for a bug. `as_mut_slice`
// and its siblings are in the POSITIVE in-place-mutator set, so taking the view
// counts as writing the receiver even when the returned alias is dropped unused
// — and that costs an honest `Verified` the merge base had.
//
// The refusal is kept, for two reasons measured right here:
//  * `w13_mut_view_then_written` is the SAME program one statement longer, and
//    the alias `s` is a binding the BLOCK owns, so a write through it is
//    `root_is_writable` = true. Narrowing on "the view is never written" needs
//    real alias tracking, not a syntactic test, or that twin becomes a false
//    Verified;
//  * `w5_mut_borrow_out` already refuses `&mut e` of an exec local in a proof
//    block whatever is done with the reference. `v.as_mut_slice()` is the
//    method-call spelling of exactly that, and upstream Verus forbids a `&mut`
//    of an exec variable in proof mode outright.
fn w13_mut_view_never_written(v: &mut Vec<u64>) {
    trust_vc::proof_block!({
        let s = v.as_mut_slice();
        trust_vc::assert!(true);
    });
}

fn w13_mut_view_then_written(v: &mut Vec<u64>) {
    trust_vc::proof_block!({
        let s = v.as_mut_slice();
        s[0] = 7u64;
    });
    trust_vc::assert!(v[0] == 7u64);
}

fn w13_get_mut_view(v: &mut Vec<u64>) {
    trust_vc::proof_block!({
        let s = v.get_mut(0);
        trust_vc::assert!(true);
    });
}

fn w13_iter_mut_view(v: &mut Vec<u64>) {
    trust_vc::proof_block!({
        let s = v.iter_mut();
        trust_vc::assert!(true);
    });
}

// NON-VACUITY for that refusal: the same view on a container the BLOCK owns is
// not a write to anything erased, and must still verify.
fn ok_mut_view_of_a_proof_local() {
    trust_vc::proof_block!({
        let mut t: Vec<u64> = Vec::new();
        let _s = t.as_mut_slice();
        trust_vc::assert!(true);
    });
}

// ... and the plain-EXEC control: outside a proof block nothing is erased.
fn ok_mut_view_in_exec_code(v: &mut Vec<u64>) {
    let _s = v.as_mut_slice();
    trust_vc::assert!(true);
}

// ===== ROUND 4, witness 14: A SPEC-MODE *PARAMETER* READ BY EXEC CODE =====
// The ghost read gate was built from the function BLOCK and never saw the
// SIGNATURE, so a mode marker on a PARAMETER read as exec. Same shape as
// witness 6, one seam over — and measured identically at the merge base and on
// the branch before this fix, so it is an inherited hole, not one this work
// opened.
fn w14_spec_param_read_by_exec(#[trust_vc::spec] s: u64) {
    let e: u64 = s;
    trust_vc::assert!(e == s);
}

// The liar twin: it came back Counterexample, which proves the solver genuinely
// held the erased parameter rather than merely failing to refute the claim.
fn w14_spec_param_read_liar(#[trust_vc::spec] s: u64) {
    let e: u64 = s;
    trust_vc::assert!(e != s);
}

fn w14_proof_param_read_by_exec(#[trust_vc::proof] s: u64) {
    let e: u64 = s;
    trust_vc::assert!(e == s);
}

fn w14_spec_param_read_in_a_call_arg(#[trust_vc::spec] s: u64) -> u64 {
    exec_identity(s)
}

fn w14_spec_param_read_in_an_exec_condition(#[trust_vc::spec] s: bool) -> u64 {
    if s {
        1u64
    } else {
        0u64
    }
}

// NON-VACUITY, three ways: an UNMARKED parameter is exec and reading it is
// ordinary; a spec parameter read by SPEC code is the whole point of having
// one; and an inner binding of the same name SHADOWS the parameter and is exec
// again.
fn ok_exec_param_read(s: u64) {
    let e: u64 = s;
    trust_vc::assert!(e == s);
}

fn ok_spec_param_read_by_spec(#[trust_vc::spec] s: u64) {
    trust_vc::assert!(s == s);
}

fn ok_exec_local_shadowing_a_spec_param(#[trust_vc::spec] s: u64) {
    let s: u64 = 3u64;
    let e: u64 = s;
    trust_vc::assert!(e == 3u64);
}
"####;

/// A macro defined nowhere in the file. It sits in a file of its own because
/// a macro whose expansion the lane cannot read refuses a `Verified` answer
/// for every function of its file.
const SRC_UNWALKABLE: &str = r####"
// FAIL CLOSED: a macro the gate can neither dispatch as a spec lane nor resolve
// as a function-local definition is refused rather than skipped. This is the
// posture the rest of the gate already takes for an unresolved place root.
fn w7_unresolvable_macro_is_refused() {
    trust_vc::proof_block!({
        some_unknown_macro!();
    });
}
"####;

fn run(func: &str) -> VerifyResult {
    run_src(SRC, func)
}

fn run_src(src: &str, func: &str) -> VerifyResult {
    let dir = std::env::temp_dir().join("trust_vc_proof_block_place_write_soundness");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{func}.rs"));
    let mut f = std::fs::File::create(&path).unwrap();
    f.write_all(src.as_bytes()).unwrap();
    drop(f);
    verify_function_from_file(path.to_str().unwrap(), func).unwrap_or_else(|e| {
        VerifyResult::Error {
            message: e.to_string(),
        }
    })
}

/// A proof-block mode violation must be REJECTED — and specifically by the mode
/// gate, not by some unrelated parse failure that would mask a regression.
fn assert_mode_rejected(func: &str, expect: &str) {
    assert_mode_rejected_in(SRC, func, expect);
}

fn assert_mode_rejected_in(src: &str, func: &str, expect: &str) {
    match run_src(src, func) {
        VerifyResult::Error { message } => assert!(
            message.contains(expect),
            "{func}: expected the mode gate to reject with {expect:?}, got: {message}"
        ),
        other => panic!(
            "{func}: a proof block's write to an EXEC place is ERASED at runtime; \
             believing it is a false Verified. Got: {other:?}"
        ),
    }
}

const WRITE: &str = "cannot assign to exec variable from proof mode";
const READ: &str = "exec code cannot read non-exec variable";

fn assert_verified(func: &str, why: &str) {
    let r = run(func);
    assert!(
        r.is_verified(),
        "{func} must still verify ({why}); got: {r:?}"
    );
}

// ---- witness 1: field write behind a name collision ----

#[test]
fn field_write_with_a_shadowing_proof_local_is_rejected() {
    assert_mode_rejected("w1_field_shadow_bypass", WRITE);
}

#[test]
fn field_write_liar_twin_is_rejected() {
    assert_mode_rejected("w1_field_shadow_liar", WRITE);
}

#[test]
fn nested_field_write_is_rejected() {
    assert_mode_rejected("w1_nested_field_write", WRITE);
}

// ---- witness 2: index write ----

#[test]
fn index_write_is_rejected() {
    assert_mode_rejected("w2_index_write_liar", WRITE);
}

// ---- witness 3: every compound assignment, shifts included ----

#[test]
fn compound_assignments_are_all_rejected() {
    for func in [
        "w3_shr_assign",
        "w3_shl_assign",
        "w3_add_assign",
        "w3_bitor_assign",
        "w3_bitand_assign",
        "w3_bitxor_assign",
        "w3_rem_assign",
    ] {
        assert_mode_rejected(func, WRITE);
    }
}

// ---- witness 4: the alias the engine itself dispatches ----

#[test]
fn the_dispatched_alias_is_gated_too() {
    assert_mode_rejected("w4_alias_bypass", WRITE);
    assert_mode_rejected("w4_alias_bare", WRITE);
}

// ---- further spellings, decided by the place resolver ----

#[test]
fn deref_param_nested_and_method_writes_are_rejected() {
    for func in [
        "w5_deref_write",
        "w5_param_write",
        "w5_nested_block",
        "w5_if_body",
        "w5_nested_proof_block",
        "w5_method_mutation",
        "w5_mut_borrow_out",
    ] {
        assert_mode_rejected(func, WRITE);
    }
}

// ---- witness 6: the read half of `let ghost` ----

#[test]
fn exec_reads_of_a_ghost_local_are_rejected() {
    for func in [
        "w6_ghost_read_by_exec",
        "w6_ghost_read_in_exec_assignment",
        "w6_tracked_read_by_exec",
        "w6_ghost_read_in_exec_call_arg",
        "w6_ghost_read_in_exec_condition",
    ] {
        assert_mode_rejected(func, READ);
    }
}

// ---- NON-VACUITY ----

#[test]
fn logical_and_or_inside_a_proof_block_still_verify() {
    assert_verified("ok_andand", "`&&` is not an assignment to `flag`");
    assert_verified("ok_oror", "`||` is not an assignment to `flag`");
    assert_verified("ok_andand_in_exec", "the exec-code control");
}

#[test]
fn joint_punct_operators_are_not_assignments() {
    assert_verified(
        "ok_joint_puncts_are_not_assignments",
        "`<<`, `>>`, `&`, `|`, `==`, `!=`, `<=`, `>=` are not writes",
    );
}

#[test]
fn ghost_and_proof_local_writes_still_verify() {
    assert_verified(
        "ok_ghost_write",
        "a ghost local is writable from proof mode",
    );
    assert_verified(
        "ok_ghost_typed_write",
        "a `Ghost<T>`-declared local is ghost mode",
    );
    assert_verified(
        "ok_proof_local_write",
        "the block owns bindings it declared itself",
    );
}

#[test]
fn proof_block_reads_of_exec_locals_still_verify() {
    assert_verified("ok_proof_reads_exec", "only WRITES are erased");
    assert_verified("ok_pure_method_on_exec", "`len` is a pure read");
}

#[test]
fn spec_reads_of_a_ghost_local_still_verify() {
    assert_verified("ok_ghost_read_by_spec", "that is what a ghost local is for");
}

#[test]
fn a_local_named_ghost_is_untouched() {
    assert_verified("ok_local_named_ghost", "`ghost` here is a binding name");
}

// ---- shadowing, both directions ----

#[test]
fn an_exec_shadow_of_a_ghost_name_loses_the_write_permission() {
    assert_mode_rejected("shadow_exec_over_ghost", WRITE);
}

/// The sibling lowering must not believe the write either — but by a DIFFERENT
/// mechanism (snapshot restore), so this asserts only "not Verified", not a
/// particular diagnostic.
#[test]
fn an_assert_by_block_write_is_not_believed() {
    let r = run("assert_by_block_write_does_not_propagate");
    assert!(
        !r.is_verified(),
        "an `assert_by!` block's write to an exec local must not reach the \
         surrounding state; got Verified"
    );
}

// ---- pattern binders ----

#[test]
fn pattern_binders_are_owned_by_the_block() {
    assert_verified("ok_closure_param_write", "a closure owns its parameter");
    assert_verified("ok_match_arm_binding", "an arm owns its pattern binding");
    assert_verified("ok_if_let_binding", "an `if let` owns its pattern binding");
}

#[test]
fn an_if_let_binding_does_not_leak_into_the_else_branch() {
    assert_mode_rejected("if_let_binding_does_not_leak_into_else", WRITE);
}

#[test]
fn a_closure_writing_an_outer_exec_local_is_rejected() {
    assert_mode_rejected("closure_writing_outer_exec_local_is_rejected", WRITE);
}

#[test]
fn a_ghost_shadow_of_an_exec_name_gains_it() {
    assert_verified(
        "shadow_ghost_over_exec",
        "the innermost binding decides the mode",
    );
}

// ---- witness 7: a function-local `macro_rules!` ----

/// SOUNDNESS-CRITICAL. `body_extract` EXPANDS single-arm zero-argument
/// function-local macros and lowers what they expand to, while `syn::visit` does
/// not descend into a macro's token stream. Every round-1 witness reappeared
/// verbatim inside one, which is the reviewer's predicted "fourth spelling" —
/// and it is not a spelling of a PLACE at all, it is a statement hidden behind
/// an expansion the gate did not perform. The gate now performs it.
#[test]
fn writes_hidden_in_a_function_local_macro_are_rejected() {
    for func in [
        "w7_macro_plain_write",
        "w7_macro_plain_write_liar",
        "w7_macro_field_write",
        "w7_macro_compound_write",
        "w7_macro_declared_inside_block",
        "w7_macro_through_the_alias",
    ] {
        assert_mode_rejected(func, WRITE);
    }
}

/// FAIL CLOSED on a macro the gate can neither dispatch as a spec lane nor
/// resolve as a local definition — the same posture it already takes for an
/// unresolved place root.
#[test]
fn an_unwalkable_macro_inside_a_proof_block_is_refused() {
    assert_mode_rejected_in(SRC_UNWALKABLE, "w7_unresolvable_macro_is_refused", WRITE);
}

#[test]
fn honest_local_macros_are_not_refused() {
    assert_verified(
        "ok_macro_writes_a_proof_local",
        "the block owns the binding the macro writes",
    );
    assert_verified("ok_macro_in_exec_code", "the plain-exec control");
}

// ---- witness 8: pure spec combinators are not writes ----

/// The METHOD arm used to be a NEGATIVE test (`!is_known_pure_struct_method`),
/// so every method not on a universal-pure allow-list counted as a write. That
/// refused six of the canonical PURE spec constructors, whose names collide with
/// `Vec`/`HashSet`/`HashMap` in-place mutators. The receiver's TYPE decides now.
#[test]
fn pure_spec_collection_combinators_are_not_writes() {
    for func in [
        "ok_seq_push",
        "ok_seq_update",
        "ok_set_insert",
        "ok_set_remove",
        "ok_map_insert",
        "ok_map_remove",
    ] {
        assert_verified(func, "a spec collection has no in-place mutator");
    }
}

/// NON-VACUITY for that relaxation: `Vec` and `Seq` lower to the SAME modelled
/// type, so this is decided by the declaration's `bounded_len` provenance bit.
#[test]
fn the_same_method_name_on_an_exec_container_is_still_a_write() {
    assert_mode_rejected("w8_vec_push_on_an_exec_param", WRITE);
    assert_mode_rejected("w8_vec_push_on_an_exec_local", WRITE);
}

// ---- witness 9: a ghost value inside an exec write's place ----

#[test]
fn a_ghost_index_in_an_exec_write_is_rejected() {
    assert_mode_rejected("w9_ghost_index_in_an_exec_write", READ);
    assert_mode_rejected("w9_ghost_index_in_an_exec_write_liar", READ);
    // The compound twin was already caught by the default walk; both spellings
    // are decided by the same code now.
    assert_mode_rejected("w9_ghost_index_compound_twin", READ);
}

#[test]
fn an_exec_index_in_an_exec_write_still_verifies() {
    assert_verified("ok_exec_index_in_an_exec_write", "the honest control");
}

// ---- witness 10: a ghost read hidden in a local macro ----

#[test]
fn ghost_reads_hidden_in_a_function_local_macro_are_rejected() {
    assert_mode_rejected("w10_ghost_read_in_a_macro", READ);
    assert_mode_rejected("w10_ghost_read_in_a_macro_liar", READ);
}

#[test]
fn an_exec_read_in_a_local_macro_still_verifies() {
    assert_verified("ok_exec_read_in_a_macro", "the non-ghost control");
}

// ---- witness 11: an exec write to a ghost PLACE ----

const GHOST_WRITE: &str = "exec code cannot mutate non-exec variable";

#[test]
fn exec_writes_to_a_ghost_place_are_rejected() {
    for func in [
        "w11_exec_writes_a_ghost_field",
        "w11_exec_writes_a_ghost_index",
        "w11_exec_writes_a_ghost_name",
    ] {
        assert_mode_rejected(func, GHOST_WRITE);
    }
}

#[test]
fn a_proof_block_may_write_a_ghost_place() {
    assert_verified(
        "ok_proof_block_writes_a_ghost_field",
        "writing ghost state is what a proof block is for",
    );
}

#[test]
fn every_route_through_an_expansion_is_walked() {
    for func in [
        "w7_macro_expands_to_a_proof_block",
        "w7_macro_inside_a_nested_proof_block",
        "w7_macro_defines_a_macro",
        "w7_mut_borrow_of_a_field",
        "w7_write_in_a_loop_body",
    ] {
        assert_mode_rejected(func, WRITE);
    }
}

#[test]
fn ghost_places_and_reads_behind_an_expansion_are_rejected() {
    assert_mode_rejected("w11_exec_writes_a_ghost_field_in_a_macro", GHOST_WRITE);
    assert_mode_rejected("w10_ghost_read_in_an_expression_macro", READ);
}

/// NON-VACUITY for the fail-closed macro rule: refusing an unwalkable macro must
/// not refuse the SPEC lanes, which is every macro trust-vc gives a name-keyed
/// meaning to.
#[test]
fn spec_macros_inside_a_proof_block_are_not_refused() {
    assert_verified(
        "ok_spec_macros_inside_a_proof_block",
        "`assert_by!`/`assert!`",
    );
    assert_verified("ok_assume_inside_a_proof_block", "`assume!`");
    assert_verified("ok_seq_macro_inside_a_proof_block", "`seq![..]`");
}

#[test]
fn a_local_macro_shadowing_a_spec_lane_name_is_refused() {
    assert_mode_rejected("w7_shadowed_spec_macro_name_writes_exec", WRITE);
}

// ---- ROUND 4, item 1: the refusal TEXT, not just the refusal ----

/// The unwalkable-macro refusal is RENDERED prose, and nothing asserted on it.
/// It was first written without its string-continuation backslashes, so
/// `format!` emitted ONE long line carrying the source file's own indentation
/// inside it (runs of fourteen spaces mid-sentence). That was fixed — and then
/// a later "restore from a byte-exact backup" step silently replayed the broken
/// form over the fix, reverting the commit, and no test noticed. The exact
/// sentence is pinned here so that cannot happen quietly again.
const UNWALKABLE_MACRO_REFUSAL: &str = "cannot assign to exec variable from proof mode: the proof \
     block invokes `some_unknown_macro!`, whose expansion this pass cannot walk \u{2014} the engine \
     lowers what a macro expands to, so a write hidden inside one would be believed while the \
     proof block is erased at runtime. Refusing fail-closed; move the statement out of the macro";

#[test]
fn the_unwalkable_macro_refusal_is_rendered_as_prose() {
    let message = match run_src(SRC_UNWALKABLE, "w7_unresolvable_macro_is_refused") {
        VerifyResult::Error { message } => message,
        other => panic!("expected the fail-closed macro refusal, got: {other:?}"),
    };
    assert!(
        message.contains(UNWALKABLE_MACRO_REFUSAL),
        "the refusal must render as prose, not as the source file's own line \
         wrapping. Expected to contain:\n{UNWALKABLE_MACRO_REFUSAL}\ngot:\n{message}"
    );
    assert!(
        !message.contains("  "),
        "a run of spaces inside a diagnostic means the string-continuation \
         backslashes were lost: {message}"
    );
}

// ---- ROUND 4, witness 12: an UNRESOLVED place root ----

/// The `None` arm of `check_place` — a place whose root the resolver cannot
/// reach — was the one disposition of this gate that failed NO named test when
/// neutralized to fail-open. Five spellings reach it: a DESTRUCTURING
/// assignment, whose LHS is an `Expr::Tuple` / `Expr::Array` / `Expr::Struct`,
/// and a deref of a CALL, which meets an `Expr::Call`.
///
/// MEASURED, and said plainly rather than overclaimed: neutralizing the arm
/// turns each witness into a DIFFERENT error, never into a `Verified` —
/// "destructuring assignment" and "assignment through a dereferenced reference"
/// are both unsupported one step later at the lowering seam. So this pins a
/// DIAGNOSTIC-quality disposition, not a false-Verified hole. It is worth
/// pinning anyway: what saves those five today is the SUPPORTED SURFACE, which
/// grows, and not the mode rule, which does not.
#[test]
fn a_place_whose_root_cannot_be_resolved_is_refused() {
    for func in [
        "w12_tuple_destructure_assign",
        "w12_slice_destructure_assign",
        "w12_struct_destructure_assign",
        "w12_unresolved_place_compound_assign",
        "w12_unresolved_place_plain_assign",
    ] {
        assert_mode_rejected(func, WRITE);
        // Specifically THAT arm, not some other rejection standing in for it.
        assert_mode_rejected(func, UNRESOLVED_PLACE);
    }
}

const UNRESOLVED_PLACE: &str = "`<unresolved place>`";

// ---- ROUND 4, item 3: a `&mut` VIEW of an exec container ----

/// INTENDED BEHAVIOUR, pinned as such. A proof block that takes a `&mut` view
/// of an exec container is refused even when the returned alias is never
/// written through, and that costs an honest `Verified` the merge base had.
/// Kept because the alias is a binding the BLOCK owns, so a write through it is
/// permitted by `root_is_writable` — narrowing on "never written" needs real
/// alias tracking, and `w13_mut_view_then_written` below is the one-statement
/// counterexample. `&mut e` of an exec local is already refused the same way
/// (`w5_mut_borrow_out`), and upstream Verus forbids a `&mut` of an exec
/// variable in proof mode outright. Disclosed as a residual over-rejection.
#[test]
fn a_mut_view_of_an_exec_container_is_refused_even_if_never_written() {
    for func in [
        "w13_mut_view_never_written",
        "w13_get_mut_view",
        "w13_iter_mut_view",
    ] {
        assert_mode_rejected(func, WRITE);
    }
}

/// The reason the refusal above is not narrowed: one statement more and the
/// same program writes through the alias, which the gate would then permit.
#[test]
fn a_mut_view_that_is_written_through_is_refused() {
    assert_mode_rejected("w13_mut_view_then_written", WRITE);
}

#[test]
fn mut_views_that_write_nothing_erased_still_verify() {
    assert_verified(
        "ok_mut_view_of_a_proof_local",
        "the block owns the container it views",
    );
    assert_verified("ok_mut_view_in_exec_code", "the plain-exec control");
}

// ---- ROUND 4, witness 14: a spec-mode PARAMETER read by exec code ----

/// SOUNDNESS-CRITICAL, and INHERITED rather than introduced: measured
/// identically at the merge base and on this branch before the fix. The ghost
/// read gate was built from the function BLOCK and never saw the SIGNATURE, so
/// `#[trust_vc::spec] s: u64` read as an ordinary exec parameter, and an exec
/// read of it was believed. Same shape as witness 6, one seam over.
#[test]
fn exec_reads_of_a_spec_mode_parameter_are_rejected() {
    for func in [
        "w14_spec_param_read_by_exec",
        "w14_spec_param_read_liar",
        "w14_proof_param_read_by_exec",
        "w14_spec_param_read_in_a_call_arg",
        "w14_spec_param_read_in_an_exec_condition",
    ] {
        assert_mode_rejected(func, READ);
    }
}

#[test]
fn honest_parameter_reads_still_verify() {
    assert_verified("ok_exec_param_read", "an unmarked parameter is exec");
    assert_verified(
        "ok_spec_param_read_by_spec",
        "that is what a spec parameter is for",
    );
    assert_verified(
        "ok_exec_local_shadowing_a_spec_param",
        "the innermost binding decides the mode",
    );
}
