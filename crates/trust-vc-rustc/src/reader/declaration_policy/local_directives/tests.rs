// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_driver;

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_attr_ir::Attribute;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::DefId;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use rustc_span::AttrId;
use trust_vc_vcir::Mode;

use super::super::{check, Recursion, RecursionOrigin};
use super::{capture, has_candidate, native_attrs, CheckedDirectives};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Temp(PathBuf);

impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

type Inspect = for<'tcx> fn(TyCtxt<'tcx>, DefId);

struct Capture {
    inspect: Inspect,
    ran: bool,
}

impl Callbacks for Capture {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        (self.inspect)(tcx, named(tcx, "Target"));
        self.ran = true;
        Compilation::Stop
    }
}

fn named(tcx: TyCtxt<'_>, name: &str) -> DefId {
    tcx.hir_crate_items(())
        .owners()
        .map(|owner| owner.def_id.to_def_id())
        .find(|owner| {
            tcx.opt_item_name(*owner)
                .is_some_and(|actual| actual.as_str() == name)
        })
        .expect("the genuine native fixture contains its named declaration")
}

/// Tool markers exercise native syntax and owner queries only. They do not
/// authenticate macro output or supply import, body, ownership or WF facts.
fn native(source: &str, inspect: Inspect, expected_diagnostic: bool) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-local-directives-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let path = directory.0.join("directives.rs");
    std::fs::write(
        &path,
        format!(
            r#"#![feature(register_tool, sized_hierarchy)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, non_snake_case)]
#[verus::internal(verus_macro)]
pub struct Other<A> {{ marker: std::marker::PhantomData<A> }}
#[verus::internal(verus_macro)]
pub fn NotNominal<A>(_value: A) {{}}
{source}
"#
        ),
    )
    .unwrap();
    let arguments = vec![
        "native-local-directive-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=native_local_directive_control".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.0.to_str().unwrap().into(),
        path.to_str().unwrap().into(),
    ];
    let mut callbacks = Capture {
        inspect,
        ran: false,
    };
    let result =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut callbacks));
    assert!(
        callbacks.ran,
        "the actual native analysis callback must run"
    );
    assert_eq!(
        result.is_err(),
        expected_diagnostic,
        "only the explicit post-diagnostic control may fail native compilation"
    );
}

fn attribute_id(attribute: &Attribute) -> Option<AttrId> {
    match attribute {
        Attribute::Unparsed(item) => Some(item.id.attr_id),
        Attribute::Parsed(_) => None,
    }
}

fn permitted_count<'tcx>(directives: &CheckedDirectives<'_, 'tcx>, tcx: TyCtxt<'tcx>) -> usize {
    directives
        .scopes
        .iter()
        .map(|scope| {
            scope
                .original
                .iter()
                .filter(|attribute| directives.permits(tcx, scope.definition, attribute))
                .count()
        })
        .sum()
}

fn preserves_remaining<'tcx>(
    directives: &CheckedDirectives<'_, 'tcx>,
    tcx: TyCtxt<'tcx>,
    scope: DefId,
) {
    let original = native_attrs(tcx, scope).unwrap();
    let expected = original
        .iter()
        .filter(|attribute| !directives.permits(tcx, scope, attribute))
        .map(attribute_id)
        .collect::<Vec<_>>();
    let remaining = directives.remaining(tcx, scope).unwrap();
    assert_eq!(
        remaining.iter().map(attribute_id).collect::<Vec<_>>(),
        expected
    );
}

fn inspect_named(tcx: TyCtxt<'_>, owner: DefId) {
    assert!(has_candidate(tcx, owner).unwrap());
    assert!(!has_candidate(tcx, named(tcx, "Other")).unwrap());
    let checked = check(tcx, owner);
    let policy = checked
        .for_owner(tcx, owner)
        .expect("actual checked nominal policy");
    let recursion = policy.nominal().unwrap().recursion();
    assert_eq!(
        recursion
            .iter()
            .map(|entry| entry.policy)
            .collect::<Vec<_>>(),
        vec![
            Recursion::Reject,
            Recursion::RejectInGround,
            Recursion::Accept
        ]
    );
    assert!(recursion
        .iter()
        .enumerate()
        .all(|(index, entry)| entry.parameter == index as u32
            && entry.origin == RecursionOrigin::ItemAttribute));
    let directives = capture(tcx, owner, &checked).expect("actual named recursion occurrences");
    assert!(directives.has_directives(tcx));
    assert_eq!(permitted_count(&directives, tcx), 3);
    preserves_remaining(&directives, tcx, owner);
    let remaining = directives.remaining(tcx, owner).unwrap();
    assert!(crate::reader::attrs::verus_attrs(&remaining).iter().any(
        |(attribute, _)| matches!(attribute, crate::reader::attrs::VerusAttr::Unknown(name)
            if name == "verifier::ext_equal")
    ));
}

fn inspect_bare(tcx: TyCtxt<'_>, owner: DefId) {
    assert!(has_candidate(tcx, owner).unwrap());
    let checked = check(tcx, owner);
    let policy = checked
        .for_owner(tcx, owner)
        .expect("actual bare parameter policy");
    let recursion = &policy.nominal().unwrap().recursion()[0];
    assert_eq!(recursion.policy, Recursion::Reject);
    assert_eq!(recursion.origin, RecursionOrigin::ParameterAttribute);
    let parameter = tcx.generics_of(owner).own_params[0].def_id;
    let directives = capture(tcx, owner, &checked).expect("actual parameter occurrences");
    assert!(directives.has_directives(tcx));
    assert_eq!(permitted_count(&directives, tcx), 2);
    assert!(directives.remaining(tcx, parameter).unwrap().is_empty());
    assert!(native_attrs(tcx, parameter)
        .unwrap()
        .iter()
        .all(|attribute| directives.permits(tcx, parameter, attribute)
            && !directives.permits(tcx, owner, attribute)));
    preserves_remaining(&directives, tcx, owner);
}

fn inspect_preserved(tcx: TyCtxt<'_>, owner: DefId) {
    let checked = check(tcx, owner);
    let policy = checked.for_owner(tcx, owner).unwrap();
    assert!(policy.nominal().unwrap().external_body());
    assert!(policy.nominal().unwrap().ext_equal_declared());
    let directives = capture(tcx, owner, &checked).unwrap();
    assert_eq!(permitted_count(&directives, tcx), 1);
    preserves_remaining(&directives, tcx, owner);
    let remaining = directives.remaining(tcx, owner).unwrap();
    let ordinary = crate::reader::attrs::item_attrs(&remaining);
    assert!(ordinary.verus_macro && ordinary.external_body);
    assert_eq!(ordinary.mode, Some(Mode::Proof));
    assert!(ordinary
        .unsupported
        .iter()
        .any(|(name, _)| name == "verifier::ext_equal"));
}

#[test]
fn native_recursion_occurrences_preserve_indices_precedence_and_other_attributes() {
    native(
        r#"
#[verus::internal(verus_macro)]
#[verifier::ext_equal]
#[verifier::accept_recursive_types(C)]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types_in_ground_variants(B)]
pub struct Target<A, B, C> { marker: std::marker::PhantomData<(A, B, C)> }
"#,
        inspect_named,
        false,
    );
    native(
        r#"
#[verus::internal(verus_macro)]
pub struct Target<#[verifier::accept_recursive_types] #[verifier::reject_recursive_types] A> {
    marker: std::marker::PhantomData<A>
}
"#,
        inspect_bare,
        false,
    );
    native(
        r#"
#[verus::internal(verus_macro)]
#[verus::internal(proof)]
#[verifier::external_body]
#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct Target<A> { marker: std::marker::PhantomData<A> }
"#,
        inspect_preserved,
        false,
    );
}

const BOUNDARY: &str = r#"
#[verus::internal(verus_macro)]
#[verifier::reject_recursive_types(A)]
pub struct Target<A> { marker: std::marker::PhantomData<A> }
"#;

fn inspect_boundaries(tcx: TyCtxt<'_>, owner: DefId) {
    let checked = check(tcx, owner);
    let directives = capture(tcx, owner, &checked).unwrap();
    let original = native_attrs(tcx, owner)
        .unwrap()
        .iter()
        .find(|attribute| directives.permits(tcx, owner, attribute))
        .unwrap();
    let cloned = (*original).clone();
    let (Attribute::Unparsed(actual), Attribute::Unparsed(copy)) = (original, &cloned) else {
        panic!("the actual recursion attribute is unparsed native syntax");
    };
    assert_eq!(actual.id.attr_id, copy.id.attr_id);
    assert_eq!(actual.span, copy.span);
    assert!(!std::ptr::eq(original, &cloned));
    assert!(!directives.permits(tcx, owner, &cloned));
    let other = named(tcx, "Other");
    assert!(!directives.permits(tcx, other, original));
    assert!(directives.remaining(tcx, other).is_none());
    assert!(capture(tcx, other, &checked).is_err());
    let other_policy = check(tcx, other);
    assert!(other_policy.for_owner(tcx, other).is_some());
    assert!(capture(tcx, owner, &other_policy).is_err());
    let function = named(tcx, "NotNominal");
    assert!(has_candidate(tcx, function).is_err());
    let function_policy = check(tcx, function);
    assert!(function_policy
        .for_owner(tcx, function)
        .unwrap()
        .nominal()
        .is_none());
    assert!(capture(tcx, function, &function_policy).is_err());
}

fn inspect_diagnostic_revocation(tcx: TyCtxt<'_>, owner: DefId) {
    let checked = check(tcx, owner);
    let directives = capture(tcx, owner, &checked).unwrap();
    let original = native_attrs(tcx, owner)
        .unwrap()
        .iter()
        .find(|attribute| directives.permits(tcx, owner, attribute))
        .unwrap();
    assert!(directives.has_directives(tcx));
    let _error = tcx.dcx().err("native local directive invalidation control");
    assert!(tcx.dcx().has_errors().is_some());
    assert!(has_candidate(tcx, owner).is_err());
    assert!(!directives.has_directives(tcx));
    assert!(!directives.permits(tcx, owner, original));
    assert!(directives.remaining(tcx, owner).is_none());
    assert!(capture(tcx, owner, &checked).is_err());
}

#[test]
fn native_recursion_views_reject_copies_wrong_owners_and_later_diagnostics() {
    native(BOUNDARY, inspect_boundaries, false);
    native(BOUNDARY, inspect_diagnostic_revocation, true);
}

fn inspect_internal_namespace(tcx: TyCtxt<'_>, owner: DefId) {
    assert!(
        has_candidate(tcx, owner).unwrap(),
        "a scheduling hint is not syntax authority"
    );
    let checked = check(tcx, owner);
    assert!(
        checked.for_owner(tcx, owner).is_some(),
        "the narrow policy parser accepts this spelling"
    );
    assert!(crate::reader::attrs::verus_parse(native_attrs(tcx, owner).unwrap()).is_err());
    let error = capture(tcx, owner, &checked)
        .err()
        .expect("raw ordinary syntax must reject it");
    assert!(error.starts_with("the original attribute language parse is unavailable:"));
}

fn inspect_duplicate(tcx: TyCtxt<'_>, owner: DefId) {
    assert!(
        has_candidate(tcx, owner).unwrap(),
        "a scheduling hint is not a checked policy"
    );
    let checked = check(tcx, owner);
    assert!(checked.for_owner(tcx, owner).is_none());
    assert!(checked.observation()["reason"]
        .as_str()
        .unwrap()
        .contains("duplicate recursion policy for a native type parameter"));
    assert!(capture(tcx, owner, &checked).is_err());
}

fn inspect_missing_name(tcx: TyCtxt<'_>, owner: DefId) {
    assert!(
        has_candidate(tcx, owner).unwrap(),
        "candidate discovery does not resolve native binders"
    );
    let checked = check(tcx, owner);
    assert!(checked.for_owner(tcx, owner).is_none());
    assert!(checked.observation()["reason"]
        .as_str()
        .unwrap()
        .contains("a recursion directive names no actual native type parameter"));
    assert!(capture(tcx, owner, &checked).is_err());
}

#[test]
fn native_recursion_views_require_ordinary_syntax_and_a_complete_policy() {
    native(
        r#"
#[verus::internal(verus_macro)]
#[verus::internal(reject_recursive_types(A))]
pub struct Target<A> { marker: std::marker::PhantomData<A> }
"#,
        inspect_internal_namespace,
        false,
    );
    native(
        r#"
#[verus::internal(verus_macro)]
#[verifier::reject_recursive_types(A)]
#[verifier::accept_recursive_types(A)]
pub struct Target<A> { marker: std::marker::PhantomData<A> }
"#,
        inspect_duplicate,
        false,
    );
    native(
        r#"
#[verus::internal(verus_macro)]
#[verifier::reject_recursive_types(B)]
pub struct Target<A> { marker: std::marker::PhantomData<A> }
"#,
        inspect_missing_name,
        false,
    );
}
