//! Actual native caller predicates and caller-owned graph-work controls.

extern crate rustc_driver;
use super::*;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Inspect(bool);

impl Callbacks for Inspect {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let owner = |name: &str| {
            tcx.hir_crate_items(())
                .owners()
                .map(|owner| owner.def_id)
                .find(|owner| {
                    tcx.opt_item_name(owner.to_def_id())
                        .is_some_and(|actual| actual.as_str() == name)
                })
                .unwrap()
        };
        let reference = |owner: LocalDefId, trait_id: DefId| {
            tcx.clauses_of(owner)
                .clauses
                .iter()
                .find_map(|(clause, _)| {
                    let mty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() else {
                        return None;
                    };
                    (predicate.polarity == mty::ClausePolarity::Positive
                        && predicate.trait_ref.def_id == trait_id)
                        .then_some(predicate.trait_ref)
                })
                .unwrap()
        };
        let actual = owner("observed");
        let required = owner("Required").to_def_id();
        let native_reference = reference(actual, required);
        let env = mty::TypingEnv::non_body_analysis(tcx, actual.to_def_id());
        assert!(matches!(
            tcx.codegen_select_candidate(env.as_query_input(native_reference)),
            Ok(rustc_middle::traits::ImplSource::Param(_))
        ));
        let allowance = super::super::MAX_BOUND_DEPENDENCIES;
        let mut remaining = allowance;
        assert!(parameter_bound(
            tcx,
            env,
            native_reference,
            actual.to_def_id(),
            &mut remaining
        )
        .unwrap());
        let used = allowance - remaining;
        assert!(used > 1);
        let mut exact = used;
        assert!(
            parameter_bound(tcx, env, native_reference, actual.to_def_id(), &mut exact).unwrap()
        );
        assert_eq!(exact, 0);
        assert!(
            parameter_bound(tcx, env, native_reference, actual.to_def_id(), &mut exact).is_err()
        );
        assert_eq!(exact, 0);
        let mut short = used - 1;
        let exhausted = parameter_bound(tcx, env, native_reference, actual.to_def_id(), &mut short)
            .unwrap_err();
        assert_eq!(short, 0);
        assert_eq!(exhausted.tag, "associated-type-dependency");
        assert!(exhausted
            .detail
            .contains("existing trait-dependency traversal grant was exhausted"));
        let wrong_arguments = reference(owner("wrong_arguments"), required);
        let other = owner("Other").to_def_id();
        let wrong_trait = reference(owner("wrong_trait"), other);
        for wrong in [wrong_arguments, wrong_trait] {
            let mut remaining = allowance;
            assert!(!parameter_bound(tcx, env, wrong, actual.to_def_id(), &mut remaining).unwrap());
            assert!(remaining < allowance);
        }
        let missing = owner("missing");
        let mut remaining = allowance;
        assert!(!parameter_bound(
            tcx,
            mty::TypingEnv::non_body_analysis(tcx, missing.to_def_id()),
            native_reference,
            missing.to_def_id(),
            &mut remaining
        )
        .unwrap());
        assert!(remaining < allowance);
        assert!(tcx.dcx().has_errors().is_none());
        self.0 = true;
        Compilation::Stop
    }
}

#[test]
fn native_associated_parameter_bounds_use_one_original_graph_ledger() {
    let directory = std::env::temp_dir().join(format!(
        "trust-vc-associated-clause-work-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let source = directory.join("test.rs");
    std::fs::write(
        &source,
        r#"#![allow(dead_code, non_snake_case)]
trait Required<A, B> {}
trait Other<A, B> {}
fn observed<T: Required<u8, u16>>() {}
fn wrong_arguments<T: Required<u16, u8>>() {}
fn wrong_trait<T: Other<u8, u16>>() {}
fn missing<T>() {}
"#,
    )
    .unwrap();
    let arguments = vec![
        "native-associated-clause-work".into(),
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
        .expect("actual native caller-bound fixture must compile");
    assert!(inspect.0);
    std::fs::remove_dir_all(directory).unwrap();
}
