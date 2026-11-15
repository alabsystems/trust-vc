//! Unit tests for the D1a `state_machine!` expansion.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use quote::ToTokens;

fn expanded(src: &str) -> File {
    let mut file = syn::parse_file(src).expect("fixture parses");
    expand_file(&mut file);
    file
}

fn rendered(src: &str) -> String {
    expanded(src).to_token_stream().to_string()
}

fn machine(body: &str) -> String {
    format!("trust_vc::state_machine!{{ X {{ {body} }} }}")
}

/// The refusal messages of a source, in order.
fn refusal_messages(src: &str) -> Vec<String> {
    refusals(&expanded(src))
        .into_iter()
        .map(|(_, msg)| msg)
        .collect()
}

fn only_refusal(src: &str) -> String {
    let messages = refusal_messages(src);
    assert_eq!(
        messages.len(),
        1,
        "expected exactly one refusal, got {messages:?}"
    );
    messages.into_iter().next().expect("one refusal")
}

fn assert_refuses(body: &str, fragment: &str) {
    let msg = only_refusal(&machine(body));
    assert!(
        msg.starts_with("state_machine! `X`: "),
        "refusal should carry the prefix: {msg}"
    );
    assert!(
        msg.contains(fragment),
        "refusal should contain {fragment:?}, got: {msg}"
    );
}

/// The body of a generated free fn, as a token string.
fn generated_fn_body(src: &str, name: &str) -> String {
    let file = expanded(src);
    for item in &file.items {
        if let Item::Fn(func) = item {
            if func.sig.ident == name {
                assert!(
                    is_generated(&func.attrs),
                    "{name} should carry the generated marker"
                );
                return func.block.to_token_stream().to_string();
            }
        }
    }
    panic!(
        "generated fn `{name}` not found in:\n{}",
        file.to_token_stream()
    );
}

fn item_names(src: &str) -> Vec<String> {
    expanded(src)
        .items
        .iter()
        .map(|item| match item {
            Item::Fn(f) => format!("fn {}", f.sig.ident),
            Item::Struct(s) => format!("struct {}", s.ident),
            Item::Impl(_) => "impl".to_string(),
            Item::Macro(m) => format!("macro {}", m.mac.path.to_token_stream()),
            Item::Use(_) => "use".to_string(),
            Item::Mod(m) => format!("mod {}", m.ident),
            other => format!("other {}", other.to_token_stream()),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// no-op

#[test]
fn a_file_without_an_item_position_invocation_is_untouched() {
    for src in [
        "fn f() {}",
        "macro_rules! state_machine { ($($t:tt)*) => {}; }\nfn f() { state_machine!(); }",
        "fn f() { let x = 1; }\nstruct S { a: u8 }",
    ] {
        let before = syn::parse_file(src).expect("parses");
        let mut after = before.clone();
        expand_file(&mut after);
        assert_eq!(
            before.to_token_stream().to_string(),
            after.to_token_stream().to_string(),
            "expand_file must be an exact no-op for {src:?}"
        );
    }
}

#[test]
fn a_locally_declared_macro_rules_invocation_is_left_alone() {
    let src = "macro_rules! state_machine { ($($t:tt)*) => {}; }\nstate_machine!{ X { fields { pub t: int } } }";
    let before = syn::parse_file(src).expect("parses");
    let mut after = before.clone();
    expand_file(&mut after);
    assert_eq!(
        before.to_token_stream().to_string(),
        after.to_token_stream().to_string(),
        "a file-local macro_rules invocation keeps HEAD behaviour"
    );
    assert!(refusals(&after).is_empty());
}

// ---------------------------------------------------------------------------
// generation

#[test]
fn an_admitted_machine_generates_the_documented_item_set() {
    let src = machine(
        "fields { pub x: int, pub y: int }
         init!{ initialize(a: int) { init x = a; init y = a; } }
         transition!{ tr1(n: int) { require n >= 0; update x = pre.x + n; } }
         readonly!{ r() { require pre.x >= 0; } }
         #[invariant] pub fn the_inv(&self) -> bool { self.x >= self.y }
         #[inductive(initialize)] fn init_ind(post: Self, a: int) { }
         #[inductive(tr1)] fn tr1_ind(pre: Self, post: Self, n: int) { }",
    );
    let names = item_names(&src);
    for expected in [
        "struct __TvcSm_X_State",
        "impl",
        "fn __TvcSm_X__initialize",
        "fn __TvcSm_X__initialize_enabled",
        "fn __TvcSm_X__tr1",
        "fn __TvcSm_X__tr1_strong",
        "fn __TvcSm_X__tr1_enabled",
        "fn __TvcSm_X__r",
        "fn __TvcSm_X__r_strong",
        "fn __TvcSm_X__r_enabled",
        "fn __TvcSm_X__init",
        "fn __TvcSm_X__next",
        "fn __TvcSm_X__next_strong",
        "fn init_ind",
        "fn tr1_ind",
    ] {
        assert!(
            names.iter().any(|n| n == expected),
            "missing {expected} in {names:?}"
        );
    }
    // Nothing else: no `Step`, `Config`, `show`, `take_step`, no `mod X`.
    assert_eq!(names.len(), 15, "unexpected extra items: {names:?}");
}

#[test]
fn the_frame_conjoins_every_field_and_an_untouched_field_keeps_its_pre_value() {
    let src = machine(
        "fields { pub x: int, pub y: int }
         transition!{ tr(n: int) { update x = pre.x + n; } }",
    );
    let body = generated_fn_body(&src, "__TvcSm_X__tr");
    assert!(body.contains("post . x == (pre . x + n)"), "{body}");
    assert!(body.contains("post . y == pre . y"), "{body}");
}

#[test]
fn a_one_sided_if_implies_and_extracts_the_implicit_else() {
    let src = machine(
        "fields { pub z: int }
         transition!{ tr(n: int) { if n > 0 { require n < 10; update z = pre.z + n; } } }",
    );
    let body = generated_fn_body(&src, "__TvcSm_X__tr");
    assert!(body.contains("! (n > 0) || (n < 10)"), "{body}");
    assert!(
        body.contains("post . z == (if (n > 0) { (pre . z + n) } else { pre . z })"),
        "{body}"
    );
}

#[test]
fn an_if_else_conjoins_both_guarded_sides() {
    let src = machine(
        "fields { pub z: int }
         transition!{ tr(b: bool) { if b { require pre.z > 0; } else { require pre.z < 0; } update z = 0; } }",
    );
    let body = generated_fn_body(&src, "__TvcSm_X__tr");
    assert!(body.contains("! (b) || (pre . z > 0)"), "{body}");
    assert!(body.contains("(b) || (pre . z < 0)"), "{body}");
}

#[test]
fn a_let_is_substituted_into_the_update() {
    let src = machine(
        "fields { pub z: int }
         transition!{ tr(n: int) { let m = pre.z + n; update z = m + 1; } }",
    );
    let body = generated_fn_body(&src, "__TvcSm_X__tr");
    assert!(body.contains("post . z == (((pre . z + n)) + 1)"), "{body}");
}

#[test]
fn a_require_after_an_update_is_still_conjoined() {
    let src = machine(
        "fields { pub z: int }
         transition!{ tr(b: bool, c: bool) { if b { update z = pre.z + 1; } require c; } }",
    );
    let body = generated_fn_body(&src, "__TvcSm_X__tr");
    assert!(body.contains("(c)"), "{body}");
    assert!(
        body.contains("post . z == (if (b) { (pre . z + 1) } else { pre . z })"),
        "{body}"
    );
}

#[test]
fn an_init_relation_takes_post_only_and_sets_every_field() {
    let src = machine(
        "fields { pub x: int, pub y: int }
         init!{ initialize(a: int) { require a >= 0; init x = a; if a > 1 { init y = a; } else { init y = 0; } } }",
    );
    let body = generated_fn_body(&src, "__TvcSm_X__initialize");
    assert!(body.contains("post . x == (a)"), "{body}");
    assert!(
        body.contains("post . y == (if (a > 1) { (a) } else { (0) })"),
        "{body}"
    );
    let file = expanded(&src);
    let init = file
        .items
        .iter()
        .find_map(|item| match item {
            Item::Fn(f) if f.sig.ident == "__TvcSm_X__initialize" => Some(f),
            _ => None,
        })
        .expect("init relation");
    assert_eq!(
        init.sig.inputs.to_token_stream().to_string(),
        "post : __TvcSm_X_State , a : int"
    );
}

#[test]
fn a_readonly_relation_carries_the_full_frame_and_joins_next() {
    let src = machine(
        "fields { pub z: int }
         readonly!{ r() { require pre.z > 0; } }",
    );
    let body = generated_fn_body(&src, "__TvcSm_X__r");
    assert!(body.contains("post . z == pre . z"), "{body}");
    let next = generated_fn_body(&src, "__TvcSm_X__next");
    assert!(next.contains("__TvcSm_X__r (pre , post)"), "{next}");
}

#[test]
fn enabled_drops_the_postconditions() {
    let src = machine(
        "fields { pub z: int }
         transition!{ tr(n: int) { require n >= 0; update z = pre.z + n; } }",
    );
    let enabled = generated_fn_body(&src, "__TvcSm_X__tr_enabled");
    assert!(enabled.contains("n >= 0"), "{enabled}");
    assert!(!enabled.contains("post"), "{enabled}");
}

#[test]
fn next_is_an_or_of_existentials_over_the_transition_parameters() {
    let src = machine(
        "fields { pub z: int }
         transition!{ tr(n: int) { update z = pre.z + n; } }
         transition!{ tr2() { update z = pre.z; } }",
    );
    let next = generated_fn_body(&src, "__TvcSm_X__next");
    assert!(
        next.contains("exists (| n : int | __TvcSm_X__tr (pre , post , n))"),
        "{next}"
    );
    assert!(next.contains("__TvcSm_X__tr2 (pre , post)"), "{next}");
    assert!(next.contains("||"), "{next}");
}

#[test]
fn a_machine_with_no_transitions_has_a_false_init_and_next() {
    let src = machine("fields { pub z: int }");
    assert_eq!(generated_fn_body(&src, "__TvcSm_X__init"), "{ false }");
    assert_eq!(generated_fn_body(&src, "__TvcSm_X__next"), "{ false }");
}

#[test]
fn the_generated_invariant_inlines_the_user_bodies() {
    let src = machine(
        "fields { pub x: int, pub y: int }
         #[invariant] pub fn a(&self) -> bool { self.x >= 0 }
         #[invariant] pub fn b(self) -> bool { self.y >= self.x }",
    );
    let file = expanded(&src);
    let block = file
        .items
        .iter()
        .find_map(|item| match item {
            Item::Impl(imp) => imp.items.iter().find_map(|i| match i {
                syn::ImplItem::Fn(m) if m.sig.ident == "invariant" => Some(m.clone()),
                _ => None,
            }),
            _ => None,
        })
        .expect("generated invariant");
    let text = block.block.to_token_stream().to_string();
    assert_eq!(text, "{ (self . x >= 0) && (self . y >= self . x) }");
    assert_eq!(
        block.sig.inputs.to_token_stream().to_string(),
        "& self",
        "the generated invariant always takes `&self`"
    );
}

#[test]
fn a_machine_with_no_invariant_has_a_true_invariant_and_needs_no_lemma() {
    let src = machine(
        "fields { pub z: int }
         transition!{ tr() { update z = pre.z; } }",
    );
    assert!(refusals(&expanded(&src)).is_empty());
    let file = expanded(&src);
    let text = file.to_token_stream().to_string();
    assert!(
        text.contains("fn invariant (& self) -> bool { true }"),
        "{text}"
    );
}

#[test]
fn the_generated_lemma_carries_the_upstream_contract_and_the_user_body() {
    let src = machine(
        "fields { pub z: int }
         init!{ c(a: int) { init z = a; } }
         transition!{ t(n: int) { update z = pre.z + n; } }
         #[invariant] pub fn inv(&self) -> bool { self.z >= 0 }
         #[inductive(c)] fn c_ind(post: Self, a: int) { let _keep = a; }
         #[inductive(t)] fn t_ind(pre: Self, post: Self, n: int) { }",
    );
    let file = expanded(&src);
    let text = file.to_token_stream().to_string();
    assert!(
        text.contains("# [trust_vc :: requires (__TvcSm_X__c (post , a))]"),
        "{text}"
    );
    assert!(
        text.contains(
            "# [trust_vc :: requires (pre . invariant () && __TvcSm_X__t_strong (pre , post , n))]"
        ),
        "{text}"
    );
    assert!(
        text.matches("# [trust_vc :: ensures (post . invariant ())]")
            .count()
            == 2,
        "{text}"
    );
    assert!(text.contains("let _keep = a ;"), "{text}");
}

#[test]
fn generated_idents_sit_on_their_source_lines() {
    let src = "\ntrust_vc::state_machine!{ X {\n    fields { pub z: int }\n    transition!{ tr() {\n        update z = pre.z;\n    } }\n    #[invariant] pub fn inv(&self) -> bool { self.z >= 0 }\n    #[inductive(tr)]\n    fn tr_lemma(pre: Self, post: Self) { }\n} }\n";
    let file = expanded(src);
    let mut seen = 0;
    for item in &file.items {
        if let Item::Fn(f) = item {
            match f.sig.ident.to_string().as_str() {
                "__TvcSm_X__tr" => {
                    assert_eq!(f.sig.ident.span().start().line, 4, "relation line");
                    seen += 1;
                }
                "tr_lemma" => {
                    assert_eq!(f.sig.ident.span().start().line, 9, "lemma line");
                    seen += 1;
                }
                _ => {}
            }
        }
    }
    assert_eq!(seen, 2);
}

// ---------------------------------------------------------------------------
// rewrite and poison

const SIMPLE: &str = "fields { pub z: int }
    transition!{ tr(n: int) { update z = pre.z + n; } }
    #[invariant] pub fn inv(&self) -> bool { self.z >= 0 }
    #[inductive(tr)] fn tr_ind(pre: Self, post: Self, n: int) { }";

fn with_client(client: &str) -> String {
    format!("{}\n{client}", machine(SIMPLE))
}

#[test]
fn client_paths_are_rewritten_to_the_generated_names() {
    let src = with_client(
        "#[trust_vc::proof]\n#[trust_vc::requires(X::State::tr(pre, post, n))]\n#[trust_vc::ensures(crate::X::State::next(pre, post))]\nfn client(pre: X::State, post: self::X::State, n: int) { X::State::tr_ind(pre, post, n); }",
    );
    let text = rendered(&src);
    assert!(
        text.contains("requires (__TvcSm_X__tr (pre , post , n))"),
        "{text}"
    );
    assert!(
        text.contains("ensures (__TvcSm_X__next (pre , post))"),
        "{text}"
    );
    assert!(
        text.contains("fn client (pre : __TvcSm_X_State , post : __TvcSm_X_State , n : int)"),
        "{text}"
    );
    assert!(text.contains("tr_ind (pre , post , n)"), "{text}");
    assert!(refusals(&expanded(&src)).is_empty());
}

#[test]
fn a_struct_literal_and_a_macro_token_stream_are_rewritten_too() {
    let src = with_client(
        "#[trust_vc::proof]\nfn client() { let s = X::State { z: 1 }; trust_vc::assert!(X::State::tr(s, s, 0)); }",
    );
    let text = rendered(&src);
    assert!(text.contains("__TvcSm_X_State { z : 1 }"), "{text}");
    assert!(
        text.contains("assert ! (__TvcSm_X__tr (s , s , 0))"),
        "{text}"
    );
}

#[test]
fn an_ungenerated_path_under_the_machine_is_poisoned() {
    for (client, fragment) in [
        (
            "fn client() { X::show::tr(); }",
            "`X::show::tr` is not generated by D1a state_machine!",
        ),
        (
            "fn client(s: X::Step) {}",
            "`X::Step` is not generated by D1a state_machine!",
        ),
        (
            "fn client() { X::State::next_by(); }",
            "`X::State::next_by` is not generated",
        ),
        (
            "fn client(s: X::State) { let _ = X::State::invariant(s); }",
            "call `.invariant()` with method syntax",
        ),
        (
            "fn client(s: X::State) { let _ = X::State::inv(s); }",
            "call `.inv()` with method syntax",
        ),
        ("use X::State;", "importing from state machine module `X`"),
    ] {
        let src = with_client(client);
        let messages = refusal_messages(&src);
        assert!(
            messages.iter().any(|m| m.contains(fragment)),
            "expected {fragment:?} for {client:?}, got {messages:?}"
        );
        // The `use` item itself is dropped; every other shape leaves a
        // poison ident in the referring item.
        if !client.starts_with("use ") {
            assert!(
                rendered(&src).contains(POISON_PREFIX),
                "{client:?} should leave a poison ident"
            );
        }
    }
}

#[test]
fn a_poison_ident_resolves_back_to_its_message() {
    let src = with_client("fn client(s: X::Step) {}");
    let file = expanded(&src);
    let ident = first_poison_ident(file.to_token_stream()).expect("poison ident");
    let msg = poison_message(&file, &ident).expect("message");
    assert!(msg.starts_with("state_machine! `X`: "), "{msg}");
    assert!(
        msg.contains("is not generated by D1a state_machine!"),
        "{msg}"
    );
}

#[test]
fn a_refused_machine_poisons_every_reference_to_it() {
    let src = format!(
        "{}\n#[trust_vc::proof]\n#[trust_vc::ensures(true)]\nfn client(s: X::State) {{ }}",
        machine("fields { pub z: nat }")
    );
    let messages = refusal_messages(&src);
    assert_eq!(messages.len(), 2, "{messages:?}");
    assert!(
        messages
            .iter()
            .all(|m| m.contains("field `z` has type `nat`")),
        "{messages:?}"
    );
    assert!(rendered(&src).contains(POISON_PREFIX));
}

#[test]
fn self_and_state_inside_the_machine_resolve_to_the_generated_struct() {
    let src = machine(
        "fields { pub z: int }
         transition!{ tr() { update z = pre.z; } }
         #[invariant] pub fn inv(&self) -> bool { self.z >= 0 }
         #[inductive(tr)] fn tr_ind(pre: Self, post: Self) { let _ = Self::tr(pre, post); let _: State = post; }",
    );
    let text = rendered(&src);
    assert!(
        text.contains("fn tr_ind (pre : __TvcSm_X_State , post : __TvcSm_X_State)"),
        "{text}"
    );
    assert!(text.contains("__TvcSm_X__tr (pre , post)"), "{text}");
    assert!(text.contains("let _ : __TvcSm_X_State = post"), "{text}");
}

#[test]
fn a_machine_in_an_inline_module_is_poisoned_not_expanded() {
    let src = format!("mod m {{ {} }}", machine("fields { pub z: int }"));
    let messages = refusal_messages(&src);
    assert_eq!(messages.len(), 1, "{messages:?}");
    assert!(
        messages[0].contains("state_machine! is only supported at the file root in D1a"),
        "{messages:?}"
    );
}

#[test]
fn the_refusal_marker_is_an_item_macro_so_the_duplicate_type_rule_still_counts_it() {
    let src = machine("fields { pub z: nat }");
    let file = expanded(&src);
    assert!(file.items.iter().any(|item| matches!(
        item,
        Item::Macro(m) if m.mac.path.is_ident(REFUSED_MARKER_MACRO)
    )));
}

// ---------------------------------------------------------------------------
// upstream-fragment refusals (order matters: upstream before D1a)

#[test]
fn upstream_diagnostics_are_reported_verbatim() {
    let cases: &[(&str, &str)] = &[
        (
            "fields { pub v: Map<int, int> } transition!{ some_name() { } } transition!{ some_name() { } }",
            "duplicate item name",
        ),
        (
            "fields { pub t: int } transition!{ tr() { birds_eye let x = 5; update t = 5; } }",
            "`birds_eye` only makes sense for tokenized state machines",
        ),
        (
            "fields { #[sharding(variable)] pub t: int }",
            "sharding strategy only makes sense for tokenized state machines",
        ),
        (
            "fields { pub t: int, pub u: int } init!{ c() { init t = 5; } }",
            "itialization procedure does not initialize field 'u'",
        ),
        (
            "fields { pub t: int } init!{ c() { init t = 5; init t = 6; } }",
            "field 't' might be initialized multiple times",
        ),
        (
            "fields { pub t: int } init!{ c(b: bool) { if b { init t = 5; } } }",
            "the else-branch does not initialize 't'",
        ),
        (
            "fields { pub t: int } init!{ c(b: bool) { if b { } else { init t = 5; } } }",
            "the if-branch does not initialize 't'",
        ),
        (
            "fields { pub t: int } init!{ c() { update t = 5; } }",
            "'update' statement not allowed in initialization",
        ),
        (
            "fields { pub t: int } init!{ c() { assert true; init t = 5; } }",
            "'assert' statement not allowed in initialization",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = 5; update t = 6; } }",
            "field 't' might be updated multiple times",
        ),
        (
            "fields { pub t: int } transition!{ tr() { init t = 5; } }",
            "'init' statement not allowed outside 'init' routine",
        ),
        (
            "fields { pub t: int } readonly!{ tr() { update t = 5; } }",
            "'update' statement not allowed in readonly transition",
        ),
        (
            "fields { pub t: int } property!{ tr() { update t = 5; } }",
            "'update' statement not allowed in property definition",
        ),
        (
            "fields { pub t: int } readonly!{ tr() { init t = 5; } }",
            "'init' statement not allowed outside 'init' routine",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update whats_this = 5; } }",
            "field 'whats_this' not found",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { let x = 5; update t = x; } }",
            "state machine transitions forbid multiple bound variables with the same name",
        ),
        (
            "fields { pub t: int } init!{ c() { init t = pre.t; } }",
            "cannot refer to `pre` in an 'init' routine",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = self.t; } }",
            "identifier `self` is meaningless in transition definition",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = post.t; } }",
            "cannot refer directly to `post` in a transition definition",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: super::Foo) { } }",
            "state machine error: `super::` path not allowed here",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = t; } }",
            "Use `pre.t` to access this field's value",
        ),
        (
            "fields { pub instance: int }",
            "'instance' is a reserved identifier in state machine definitions",
        ),
        (
            "fields { pub param_token_a: int }",
            "identifiers starting with 'param_token_' are reserved identifiers",
        ),
        (
            "fields { pub t: int } transition!{ tr() { let instance = 5; update t = instance; } }",
            "'instance' is a reserved identifier",
        ),
        (
            "fields { pub t: int } transition!{ tr(instance: int) { update t = instance; } }",
            "'instance' is a reserved identifier",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { update t = x; } } #[inductive(tr)] pub fn l1(pre: Self, post: Self, x: int) {} #[inductive(tr)] pub fn l2(pre: Self, post: Self, x: int) {}",
            "duplicate 'inductive' lemma",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { update t = x; } } #[invariant] pub fn the_inv(self) -> bool { self.t == 5 }",
            "missing inductiveness proofs for",
        ),
        (
            "fields { pub t: int } readonly!{ tr(x: int) { } } #[inductive(tr)] pub fn l(pre: Self, post: Self, x: int) {}",
            "'inductive' lemma does not make sense for a 'readonly' transition",
        ),
        (
            "fields { pub t: int } property!{ tr(x: int) { } } #[inductive(tr)] pub fn l(pre: Self, post: Self, x: int) {}",
            "'inductive' lemma does not make sense for a 'property' definition",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tr)] pub fn l(pre: Self, post: Self, y: int) {}",
            "params for 'inductive' lemma should be: `pre: Self, post: Self, x: int`",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tro)] pub fn l(pre: Self, post: Self, x: int) {}",
            "could not find transition `tro`",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tr)] pub fn l<T>(pre: Self, post: Self, x: int) {}",
            "should have no generic parameters",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tr)] pub fn l(pre: Self, post: Self, x: int) -> bool { true }",
            "should have no return type",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tr)] pub fn l(pre: Self, post: Self, x: int) { requires(true); }",
            "the precondition and postcondition are implicit",
        ),
        (
            "fields { pub t: int } init!{ c(x: int) { init t = x; } } #[invariant] #[inductive(c)] pub fn the_inv(self) -> bool { true }",
            "conflicting attributes",
        ),
        (
            "fields { pub t: int } #[invariant] #[verifier::spec] pub fn the_inv(self) -> bool { true }",
            "an invariant fn is implied to be 'spec'; it should not be explicitly labelled",
        ),
        (
            "fields { #[verifier::spec] pub t: int }",
            "a state field is implied to be 'spec'; it should not be explicitly labelled",
        ),
        (
            "fields { pub t: int } init!{ c(x: int) { init t = x; } } #[invariant] pub fn the_inv(self) -> bool { true } #[inductive(c)] #[verifier::proof] pub fn l(post: Self, x: int) {}",
            "an inductivity lemma is implied to be 'proof'; it should not be explicitly labelled",
        ),
        (
            "fields { pub t: int } #[invariant] pub fn the_inv(x: int) -> bool { true }",
            "an invariant function must take 1 argument (self)",
        ),
        (
            "fields { pub t: int } #[invariant] pub fn the_inv(self) -> int { 5 }",
            "an invariant function must return a bool",
        ),
        (
            "fields { pub t: int } #[invariant] pub fn the_inv<V>(self) -> bool { true }",
            "an invariant function must take 0 type arguments",
        ),
        (
            "fields { pub t: int } #[invariant] fn the_inv(self) -> bool { true }",
            "#[invariant] fn must be be marked `pub`",
        ),
        (
            "fields { pub t: int } fields { pub x: int }",
            "Expected only one declaration of `fields` block",
        ),
        ("", "the 'fields' declaration was not found"),
        (
            "fields { pub t: int } const C: int = 3;",
            "this item is not supported",
        ),
        (
            "fields { pub t: int } transition!{ tr() { if let 5 = pre.t { } } }",
            "transition definitions do not support if-let conditionals",
        ),
        (
            "fields { pub t: int } bogus!{ tr() { } }",
            "unrecognized macro for definiting a transition",
        ),
        (
            "fields { pub t: int } pub struct Bogus { }",
            "state_machine macro only supports the declaration of a `Label` and `InitLabel` types",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = my_macro!(); } }",
            "macro not allowed in transition expression",
        ),
    ];
    for (body, fragment) in cases {
        assert_refuses(body, fragment);
    }
}

#[test]
fn a_generic_machine_reports_the_upstream_non_type_param_error_first() {
    let src = "trust_vc::state_machine!{ X<'a> { fields { pub t: int } } }";
    assert!(only_refusal(src).contains("Only generic type parameters are supported"));
}

// ---------------------------------------------------------------------------
// D1a feature refusals

#[test]
fn d1a_feature_refusals_carry_their_pinned_text() {
    let cases: &[(&str, &str)] = &[
        (
            "fields { pub t: int } transition!{ tr() { assert pre.t >= 0; update t = 1; } }",
            "`assert` in a transition is not yet supported",
        ),
        (
            "fields { pub t: int } property!{ p() { require pre.t >= 0; } }",
            "`property!` is not yet supported",
        ),
        (
            "fields { pub t: int } transition!{ tr(b: bool) { match b { _ => { update t = 1; } } } }",
            "`match` in a transition is not yet supported",
        ),
        (
            "fields { pub t: int } transition!{ tr(b: bool) { require let true = b; update t = 1; } }",
            "`require let` / `assert let` are not yet supported",
        ),
        (
            "fields { pub t: int } transition!{ tr() { add t += (1); } }",
            "'add' statement not allowed for field with sharding strategy 'variable'",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t.g = 1; } }",
            "sub-field/index `update t…` is not yet supported",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: (int, int)) { update t = 1; } }",
            "parameter `x` has type `(int , int)`",
        ),
        (
            "fields { pub t: Seq<int> }",
            "field `t` has collection type `Seq<int>`; collection-valued fields need extensional equality",
        ),
        (
            "fields { pub t: u32 }",
            "field `t` has machine-integer type `u32`",
        ),
        ("fields { pub t: nat }", "field `t` has type `nat`"),
        (
            "fields { pub t: f64 }",
            "field `t` has type `f64`, which is not a file-local datatype admitted by D1a",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = pre.t / 2; } }",
            "expression form `pre . t / 2` is not supported in a D1a transition body",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = pre.t % 2; } }",
            "expression form",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { update t = x as int; } }",
            "expression form",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = 1u32; } }",
            "expression form",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = pre; } }",
            "`pre` may only be used as `pre.<field>`",
        ),
        (
            "fields { pub t: int } transition!{ tr() { update t = unknown_fn(1); } }",
            "call to `unknown_fn` is not supported",
        ),
        (
            "fields { pub t: int } transition!{ tr(pre_x: int) { let p: u8 = 1; update t = 1; } }",
            "let type `u8` is not supported (only `int`/`bool` annotations)",
        ),
        (
            "fields { pub t: int } transition!{ tr(b: bool) { let (p, q) = (1, 2); update t = 1; } }",
            "is not supported; bind a single identifier",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tr)] #[trust_vc::requires(false)] pub fn l(pre: Self, post: Self, x: int) {}",
            "is not allowed on an inductive lemma",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tr)] #[trust_vc::external_body] pub fn l(pre: Self, post: Self, x: int) {}",
            "is not allowed on an inductive lemma",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tr)] #[cfg_attr(any(), trust_vc::requires(false))] pub fn l(pre: Self, post: Self, x: int) {}",
            "is not allowed on an inductive lemma",
        ),
        (
            "fields { pub t: int } transition!{ tr(x: int) { } } #[inductive(tr)] pub fn l(pre: Self, post: Self, x: int) { trust_vc::requires!(false); }",
            "requires!/ensures!/recommends!/decreases! inside an inductive lemma body are not allowed",
        ),
        (
            "fields { pub t: int } #[invariant] #[trust_vc::opaque] pub fn the_inv(self) -> bool { true }",
            "is not allowed on an invariant fn",
        ),
        (
            "fields { pub t: int } #[invariant] pub fn the_inv(self) -> bool { let x = 1; x >= 0 }",
            "invariant `the_inv` body must be a single expression",
        ),
        (
            "fields { pub t: int } fn helper() -> int { 3 }",
            "helper fn `helper` inside state_machine! is not yet supported",
        ),
        (
            "fields { pub t: int } transition!{ tr(post: int) { update t = 1; } }",
            "'post' is a reserved identifier in state machine definitions",
        ),
        (
            "fields { pub t: int } transition!{ tr(pre: int) { update t = 1; } }",
            "`pre` is reserved (pre/post/self/Self)",
        ),
        (
            "fields { pub __TvcSm_x: int }",
            "generated item `__TvcSm_x` collides with an existing item",
        ),
    ];
    for (body, fragment) in cases {
        assert_refuses(body, fragment);
    }
}

#[test]
fn a_generic_machine_is_refused_when_its_params_are_types() {
    let src = "trust_vc::state_machine!{ X<T> { fields { pub t: int } } }";
    assert!(only_refusal(src).contains("generic state machines are not yet supported"));
}

#[test]
fn labels_and_machine_attributes_are_refused() {
    let src = "trust_vc::state_machine!{ X { fields { pub t: int } pub struct Label { } } }";
    assert!(
        only_refusal(src).contains("transition labels (`Label`/`InitLabel`) are not yet supported")
    );
    let src = "trust_vc::state_machine!{ #[verifier::reject_recursive_types(T)] X { fields { pub t: int } } }";
    let msg = only_refusal(src);
    assert!(
        msg.contains("attributes on state_machine! are not yet supported"),
        "{msg}"
    );
}

#[test]
fn a_tokenized_machine_and_an_unresolved_bare_invocation_are_poisoned() {
    let msg = only_refusal("trust_vc::tokenized_state_machine!{ X { fields { pub t: int } } }");
    assert!(
        msg.contains("tokenized_state_machine! is not yet supported"),
        "{msg}"
    );
    let msg = only_refusal("state_machine!{ X { fields { pub t: int } } }");
    assert!(
        msg.contains("bare state_machine! is not resolved to trust_vc here; write `trust_vc::state_machine!`"),
        "{msg}"
    );
    let msg = only_refusal("m::state_machine!{ X { fields { pub t: int } } }");
    assert!(
        msg.contains(
            "state_machine! via `m::state_machine` is not trust_vc's macro and is not verified"
        ),
        "{msg}"
    );
    let msg =
        only_refusal("use foreign::state_machine;\nstate_machine!{ X { fields { pub t: int } } }");
    assert!(
        msg.contains("bare state_machine! is not resolved to trust_vc here"),
        "{msg}"
    );
    let msg =
        only_refusal("mod trust_vc { }\ntrust_vc::state_machine!{ X { fields { pub t: int } } }");
    assert!(
        msg.contains("bare state_machine! is not resolved to trust_vc here")
            || msg.contains("is not trust_vc's macro"),
        "{msg}"
    );
}

#[test]
fn a_datatype_field_is_admitted_only_when_it_is_modeled_completely() {
    let ok = format!(
        "#[derive(PartialEq, Eq)] pub enum Mode {{ Idle, Busy(int) }}\n{}",
        machine(
            "fields { pub m: Mode }
             transition!{ tr(v: int) { update m = Mode::Busy(v); } }"
        )
    );
    assert!(
        refusals(&expanded(&ok)).is_empty(),
        "{:?}",
        refusal_messages(&ok)
    );
    let body = generated_fn_body(&ok, "__TvcSm_X__tr");
    assert!(body.contains("post . m == (Mode :: Busy (v))"), "{body}");

    let manual_eq = format!(
        "pub struct Liar {{ pub a: int }}\nimpl PartialEq for Liar {{ fn eq(&self, _o: &Self) -> bool {{ false }} }}\n{}",
        machine("fields { pub s: Liar }")
    );
    assert!(
        refusal_messages(&manual_eq)[0].contains("hand-written PartialEq"),
        "{:?}",
        refusal_messages(&manual_eq)
    );

    let recursive = format!(
        "pub enum L {{ Nil, Cons(L) }}\n{}",
        machine("fields { pub l: L }")
    );
    assert!(
        refusal_messages(&recursive)[0].contains("not a file-local datatype admitted by D1a"),
        "{:?}",
        refusal_messages(&recursive)
    );

    let generic = format!(
        "pub struct G<T> {{ pub a: T }}\n{}",
        machine("fields { pub g: G }")
    );
    assert!(
        refusal_messages(&generic)[0].contains("not a file-local datatype admitted by D1a"),
        "{:?}",
        refusal_messages(&generic)
    );

    let machine_int_inside = format!(
        "pub struct W {{ pub a: u8 }}\n{}",
        machine("fields { pub w: W }")
    );
    assert!(
        refusal_messages(&machine_int_inside)[0]
            .contains("not a file-local datatype admitted by D1a"),
        "{:?}",
        refusal_messages(&machine_int_inside)
    );
}

#[test]
fn a_spec_fn_call_is_admitted_only_at_the_file_root_with_an_admitted_signature() {
    let ok = format!(
        "#[trust_vc::spec]\npub fn bump(v: int) -> int {{ v + 1 }}\n{}",
        machine(
            "fields { pub z: int }
             transition!{ tr() { update z = bump(pre.z); } }"
        )
    );
    assert!(
        refusals(&expanded(&ok)).is_empty(),
        "{:?}",
        refusal_messages(&ok)
    );

    let machine_int_sig = format!(
        "#[trust_vc::spec]\npub fn bump(v: u32) -> u32 {{ v + 1 }}\n{}",
        machine(
            "fields { pub z: int }
             transition!{ tr() { update z = bump(pre.z); } }"
        )
    );
    assert!(
        refusal_messages(&machine_int_sig)[0].contains("call to `bump` is not supported"),
        "{:?}",
        refusal_messages(&machine_int_sig)
    );

    let not_spec = format!(
        "pub fn bump(v: int) -> int {{ v + 1 }}\n{}",
        machine(
            "fields { pub z: int }
             transition!{ tr() { update z = bump(pre.z); } }"
        )
    );
    assert!(
        refusal_messages(&not_spec)[0].contains("call to `bump` is not supported"),
        "{:?}",
        refusal_messages(&not_spec)
    );

    let shadowed = format!(
        "#[trust_vc::spec]\npub fn bump(v: int) -> int {{ v + 1 }}\n{}",
        machine(
            "fields { pub z: int }
             transition!{ tr(bump: int) { update z = bump(pre.z); } }"
        )
    );
    assert!(
        refusal_messages(&shadowed)[0].contains("is both a parameter/let and a called function"),
        "{:?}",
        refusal_messages(&shadowed)
    );
}

#[test]
fn two_machines_in_one_file_generate_disjoint_names() {
    let src = format!(
        "{}\n{}",
        machine(
            "fields { pub z: int }
             transition!{ tr1() { update z = pre.z; } }"
        ),
        "trust_vc::state_machine!{ Y { fields { pub z: int } transition!{ tr1() { update z = pre.z; } } } }"
    );
    assert!(
        refusals(&expanded(&src)).is_empty(),
        "{:?}",
        refusal_messages(&src)
    );
    let names = item_names(&src);
    assert!(names.iter().any(|n| n == "fn __TvcSm_X__tr1"));
    assert!(names.iter().any(|n| n == "fn __TvcSm_Y__tr1"));
    assert!(names.iter().any(|n| n == "struct __TvcSm_X_State"));
    assert!(names.iter().any(|n| n == "struct __TvcSm_Y_State"));
}

#[test]
fn a_machine_name_that_collides_with_a_file_item_is_refused() {
    let src = format!(
        "pub struct X {{ pub a: int }}\n{}",
        machine("fields { pub z: int }")
    );
    assert!(
        refusal_messages(&src)[0].contains("machine name `X` collides with another item named `X`"),
        "{:?}",
        refusal_messages(&src)
    );
}

#[test]
fn a_lemma_name_that_is_not_file_unique_is_refused() {
    let src = format!("fn tr_ind() {{}}\n{}", machine(SIMPLE));
    assert!(
        refusal_messages(&src)[0].contains("lemma name `tr_ind` is not unique in this file"),
        "{:?}",
        refusal_messages(&src)
    );
}

#[test]
fn machine_lemmas_lists_every_generated_lemma_of_an_admitted_machine() {
    let src = machine(
        "fields { pub z: int }
         init!{ c(a: int) { init z = a; } }
         transition!{ t(n: int) { update z = pre.z + n; } }
         #[invariant] pub fn inv(&self) -> bool { self.z >= 0 }
         #[inductive(c)] fn c_ind(post: Self, a: int) { }
         #[inductive(t)] fn t_ind(pre: Self, post: Self, n: int) { }",
    );
    let file = syn::parse_file(&src).expect("parses");
    let mut lemmas = machine_lemmas(&file);
    lemmas.sort();
    assert_eq!(
        lemmas,
        vec![
            ("X".to_string(), "c_ind".to_string(), "init"),
            ("X".to_string(), "t_ind".to_string(), "transition"),
        ]
    );
}

#[test]
fn a_client_inside_an_inline_module_is_refused_rather_than_left_to_fail_late() {
    let src = format!(
        "{}\nmod m {{ #[trust_vc::proof] #[trust_vc::requires(crate::X::State::tr(pre, post, n))] #[trust_vc::ensures(true)] fn client(pre: crate::X::State, post: crate::X::State, n: int) {{}} }}",
        machine(SIMPLE)
    );
    let messages = refusal_messages(&src);
    assert!(
        messages
            .iter()
            .any(|m| m.contains("from inside an inline module is not supported in D1a")),
        "{messages:?}"
    );
    assert!(rendered(&src).contains(POISON_PREFIX));
}

#[test]
fn a_bare_name_imported_from_a_machine_module_is_poisoned() {
    let src = format!(
        "{}\nuse X::State;\nfn client(s: State) {{ let _ = s; }}",
        machine(SIMPLE)
    );
    let text = rendered(&src);
    assert!(
        !text.contains("use X"),
        "the import itself is dropped: {text}"
    );
    assert!(
        text.contains("fn client (s : __trust_vc_sm_poison_"),
        "the imported bare name must be poisoned: {text}"
    );
    let messages = refusal_messages(&src);
    assert!(
        messages
            .iter()
            .all(|m| m.contains("importing from state machine module `X` is not supported")),
        "{messages:?}"
    );
}

#[test]
fn two_machines_with_the_same_name_are_both_refused() {
    let src = format!("{}\n{}", machine(SIMPLE), machine(SIMPLE));
    let messages = refusal_messages(&src);
    assert_eq!(messages.len(), 2, "{messages:?}");
    assert!(
        messages
            .iter()
            .all(|m| m.contains("generated item `__TvcSm_X_State` collides with an existing item")),
        "{messages:?}"
    );
}

#[test]
fn a_user_item_carrying_the_generated_prefix_refuses_every_machine() {
    let src = format!("struct __TvcSm_Sneaky {{ a: int }}\n{}", machine(SIMPLE));
    assert!(
        refusal_messages(&src)[0].contains("generated item `__TvcSm_Sneaky` collides"),
        "{:?}",
        refusal_messages(&src)
    );
}
