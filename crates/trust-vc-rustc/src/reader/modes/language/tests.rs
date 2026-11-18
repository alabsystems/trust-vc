//! Real native contexts, not constructed Clean-mode or ownership tokens.

extern crate rustc_driver;
use super::*;
use crate::reader::declaration_modes::DeclarationModes;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Inspect(bool);

impl Callbacks for Inspect {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let definition = |name: &str| {
            tcx.hir_crate_items(())
                .owners()
                .map(|owner| owner.def_id)
                .find(|owner| {
                    tcx.opt_item_name(owner.to_def_id())
                        .is_some_and(|actual| actual.as_str() == name)
                })
                .unwrap()
        };
        let legacy = definition("Legacy");
        let other = definition("Other");
        let modern = definition("Modern");
        let returns = definition("WrongReturn");
        let external = definition("Ignored");
        let default = DeclarationModes::new(tcx);
        assert!(matches!(default.check(legacy), ModeCheck::Unknown(_)));
        let current = DeclarationModes::with_legacy_policy(tcx, true);
        let facts = match current.check(legacy) {
            ModeCheck::Clean(facts) => facts,
            result => panic!("the actual legacy scalar binding must complete: {result:?}"),
        };
        let language = facts.language.as_ref().unwrap();
        assert!(language.legacy());
        language.checked(&current, legacy, legacy).unwrap();
        let allowance = 1_000_000usize;
        let mut remaining = allowance;
        language
            .checked_with_work(&current, legacy, legacy, &mut remaining)
            .unwrap();
        let used = allowance - remaining;
        assert!(used > 0);
        let mut exact = used;
        language
            .checked_with_work(&current, legacy, legacy, &mut exact)
            .unwrap();
        assert_eq!(exact, 0);
        assert!(language
            .checked_with_work(&current, legacy, legacy, &mut exact)
            .is_err());
        assert_eq!(exact, 0);
        let mut short = used - 1;
        assert!(language
            .checked_with_work(&current, legacy, legacy, &mut short)
            .is_err());
        assert!(short < used - 1);
        let mut wrong = allowance;
        assert!(language
            .checked_with_work(&current, other, other, &mut wrong)
            .is_err());
        assert!(wrong < allowance);

        // The actual native attributes, including nested parser tokens,
        // retain their full values/order/spans under the work adapter.
        let metered = definition("MeteredAttributes");
        let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(metered));
        let expected = attrs::verus_attrs(attributes);
        let mut work = allowance;
        assert_eq!(
            attrs::verus_attrs_with_work(attributes, &mut work).unwrap(),
            expected
        );
        let parsed_cost = allowance - work;
        let mut exact_parse = parsed_cost;
        assert_eq!(
            attrs::verus_attrs_with_work(attributes, &mut exact_parse).unwrap(),
            expected
        );
        assert_eq!(exact_parse, 0);
        assert!(attrs::verus_attrs_with_work(attributes, &mut exact_parse).is_err());
        let mut short_parse = parsed_cost - 1;
        assert!(attrs::verus_attrs_with_work(attributes, &mut short_parse).is_err());
        let mut item_work = allowance;
        assert_eq!(
            format!(
                "{:?}",
                attrs::item_attrs_with_work(attributes, &mut item_work).unwrap()
            ),
            format!("{:?}", attrs::item_attrs(attributes))
        );
        let mut comparison = allowance;
        attrs::charge_comparison(&expected, &expected, &mut comparison).unwrap();
        assert!(comparison < allowance);
        assert!(attrs::charge_comparison(&expected, &expected, &mut 0).is_err());

        // verus::ignored is dispatched as Unknown after its path. Neither
        // parser inspects/copies that unrelated delimited string payload.
        let mut costs = Vec::new();
        for name in ["SmallIgnoredPayload", "LargeIgnoredPayload"] {
            let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(definition(name)));
            let mut work = allowance;
            assert_eq!(
                attrs::verus_attrs_with_work(attributes, &mut work).unwrap(),
                attrs::verus_attrs(attributes)
            );
            costs.push(allowance - work);
        }
        assert!(costs[0] > 0);
        assert_eq!(
            costs[0], costs[1],
            "ignored payload length must not become a shared-work tax"
        );

        // The actual datatype/field route uses the same native attributes,
        // mode rules and full error text; formatting cannot escape the work
        // account merely because collection is about to reject the graph.
        let datatype = definition("MeteredFields");
        let datatype_attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(datatype));
        let mut datatype_work = allowance;
        assert_eq!(
            format!(
                "{:?}",
                attrs::item_attrs_with_work(datatype_attributes, &mut datatype_work).unwrap()
            ),
            format!("{:?}", attrs::item_attrs(datatype_attributes))
        );
        assert!(datatype_work < allowance);
        let native = tcx.adt_def(datatype);
        for (name, expected_mode) in [("logical", Mode::Spec), ("kept", Mode::Exec)] {
            let field = native
                .all_fields()
                .find(|field| field.name.as_str() == name)
                .unwrap();
            let at = tcx.def_span(field.did);
            assert_eq!(
                crate::reader::datatypes::field_mode(tcx, field, at).unwrap(),
                expected_mode
            );
            let mut work = allowance;
            assert_eq!(
                crate::reader::datatypes::field_mode_with_work(tcx, field, at, &mut work).unwrap(),
                expected_mode
            );
            let mut exact = allowance - work;
            assert_eq!(
                crate::reader::datatypes::field_mode_with_work(tcx, field, at, &mut exact).unwrap(),
                expected_mode
            );
            assert_eq!(exact, 0);
            assert!(
                crate::reader::datatypes::field_mode_with_work(tcx, field, at, &mut exact).is_err()
            );
        }
        let rejected = native
            .all_fields()
            .find(|field| field.name.as_str() == "rejected")
            .unwrap();
        let at = tcx.def_span(rejected.did);
        let original_error = crate::reader::datatypes::field_mode(tcx, rejected, at).unwrap_err();
        let mut error_work = allowance;
        let current_error =
            crate::reader::datatypes::field_mode_with_work(tcx, rejected, at, &mut error_work)
                .unwrap_err();
        assert_eq!(current_error.tag, original_error.tag);
        assert_eq!(current_error.detail, original_error.detail);
        assert_eq!(current_error.span, original_error.span);
        let mut parser_only = allowance;
        attrs::verus_attrs_with_work(
            tcx.hir_attrs(tcx.local_def_id_to_hir_id(rejected.did.as_local().unwrap())),
            &mut parser_only,
        )
        .unwrap();
        let mut before_format = 1 + allowance - parser_only;
        let limited =
            crate::reader::datatypes::field_mode_with_work(tcx, rejected, at, &mut before_format)
                .unwrap_err();
        assert_eq!(limited.tag, "field-mode-work");
        let expected_text = format!("native field-mode capture failed: {original_error:?}");
        let mut format_work = allowance;
        attrs::charge_format(
            format_args!("native field-mode capture failed: {original_error:?}"),
            &mut format_work,
        )
        .unwrap();
        let used = allowance - format_work;
        assert!(used >= expected_text.len());
        let mut exact = used;
        attrs::charge_format(
            format_args!("native field-mode capture failed: {original_error:?}"),
            &mut exact,
        )
        .unwrap();
        assert_eq!(exact, 0);
        let mut short = used - 1;
        assert!(attrs::charge_format(
            format_args!("native field-mode capture failed: {original_error:?}"),
            &mut short
        )
        .is_err());
        assert!(attrs::charge_format(
            format_args!("native field-mode capture failed: {original_error:?}"),
            &mut 0
        )
        .is_err());

        assert!(language.checked(&current, other, other).is_err());
        assert!(language.checked(&default, legacy, legacy).is_err());
        assert_eq!(facts.local_declarations.len(), 1);
        let binding = facts.local_declarations.values().next().unwrap();
        assert_eq!(binding.declared.mode, Mode::Spec);
        assert_eq!(binding.effective, Mode::Spec);
        let body = tcx.hir_body_owned_by(legacy);
        let hir::ExprKind::Block(block, None) = body.value.kind else {
            panic!("native block")
        };
        let hir::StmtKind::Let(local) = block.stmts[0].kind else {
            panic!("native declaration")
        };
        let init = local.init.unwrap();
        let row = facts
            .expressions
            .observations()
            .find(|row| std::ptr::eq(row.expression, init))
            .unwrap();
        assert_eq!(row.context.outer, Mode::Exec);
        assert_eq!(row.context.expected, Mode::Spec);
        assert!(!row.context.block_ghost);
        assert!(!row.context.uses_ghost_blocks);
        assert_eq!(row.result, Mode::Exec);
        assert_eq!(row.native_type, tcx.types.u8);
        assert!(matches!(current.check(modern), ModeCheck::Error(error)
            if error.message == msg::EXEC_INITIALIZES_NON_EXEC));
        assert!(matches!(current.check(returns), ModeCheck::Error(error)
            if error.message == msg::RETURN_FROM_NON_EXEC));
        assert!(matches!(current.check(external), ModeCheck::Unknown(_)));
        assert!(tcx.dcx().has_errors().is_none());
        self.0 = true;
        Compilation::Stop
    }
}

#[test]
fn native_legacy_context_is_current_and_separate_from_outer_and_block_modes() {
    let directory = std::env::temp_dir().join(format!(
        "trust-vc-legacy-context-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let source = directory.join("test.rs");
    std::fs::write(
        &source,
        r#"#![feature(register_tool, stmt_expr_attributes)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, non_snake_case)]
fn Legacy() { #[verifier::spec] let value: u8 = 1; }
fn Other() {}
#[verifier::proof_note("an actual parsed payload")]
#[verifier::unknown(foo(bar(1)), 2)]
fn MeteredAttributes() {}
#[verus::ignored("small")]
fn SmallIgnoredPayload() {}
#[verus::ignored("LARGE_IGNORED_ATTRIBUTE_PAYLOAD")]
fn LargeIgnoredPayload() {}
#[verus::internal(verus_macro)]
struct MeteredFields {
    #[verifier::spec]
    logical: u8,
    #[verifier::exec]
    kept: u8,
    #[verifier::custom_err("line\n\t\\tail")]
    rejected: u8,
}
#[verus::internal(verus_macro)]
fn Modern() { #[verifier::spec] let value: u8 = 1; }
fn WrongReturn(#[verifier::spec] condition: bool) -> u8 {
    if condition { return 0; }
    1
}
#[verifier::external]
fn Ignored() {}
"#
        .replace("LARGE_IGNORED_ATTRIBUTE_PAYLOAD", &"x".repeat(16_384)),
    )
    .unwrap();
    let arguments = vec![
        "native-legacy-context".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.to_str().unwrap().into(),
        source.to_str().unwrap().into(),
    ];
    let mut inspect = Inspect(false);
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut inspect))
        .expect("the original native context fixture must compile");
    assert!(inspect.0);
    std::fs::remove_dir_all(directory).unwrap();
}
