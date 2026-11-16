// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Invalid ordinary diagnostic data cannot become a partial user refutation.

use super::*;
use crate::reader::{read_crate, ReadOptions};
use crate::verdict::{SiteCounts, Verdict};
use crate::verify::{self, Report, VerifyOptions};
use trust_vc_vcir::vcgen::{CheckKind, FnVcs};
use trust_vc_vcir::SpanId;

#[test]
fn native_unwind_missing_condition_source_refuses_without_failure_credit() {
    native::run(
        r#"
#[verus::internal(verus_macro)]
fn Conditional(callee_guard: bool) {
    unwind_builtin_fixture::no_unwind_when(callee_guard);
}
#[verus::internal(verus_macro)]
fn Bad(flag: bool) {
    unwind_builtin_fixture::no_unwind_when(flag);
    Conditional(!flag);
}
"#,
        |tcx, read| {
            clean(read);
            // Obtain a fresh actual native read before invalidating only an
            // ordinary source-span observation. No source or capability changes.
            let mut invalid = read_crate(tcx, ReadOptions::default());
            clean(&invalid);
            let caller = function(tcx, &invalid, "Bad").id;
            let callee = function(tcx, &invalid, "Conditional").id;
            let generated = trust_vc_vcir::vcgen::generate(&invalid.krate);
            assert_eq!(generated.fns.len(), 2);
            for declaration in &invalid.krate.fns {
                assert!(
                    matches!(generated.get(declaration.id), Some(FnVcs::Checks(_))),
                    "{generated:?}"
                );
            }
            let Some(FnVcs::Checks(checks)) = generated.get(caller) else {
                unreachable!()
            };
            assert_eq!(checks.len(), 1);
            let CheckKind::Unwind {
                call,
                callee: selected,
            } = &checks[0].kind
            else {
                panic!("the malformed observation must affect a real unwind check")
            };
            assert_eq!(*selected, callee);
            assert!(!checks[0].approximate && !checks[0].order_unknown);
            let call = invalid.span(*call).unwrap();
            assert!(!call.is_dummy());
            assert_eq!(
                tcx.sess.source_map().span_to_snippet(call).unwrap(),
                "Conditional(!flag)"
            );

            let target = invalid
                .krate
                .fns
                .iter_mut()
                .find(|decl| decl.id == callee)
                .unwrap();
            let Some(UnwindSpec::NoUnwindWhen(condition)) = &mut target.unwind else {
                panic!("the actual callee condition must be present before invalidation")
            };
            condition.span = SpanId(u32::MAX);
            assert!(invalid.span(SpanId(u32::MAX)).is_none());
            assert!(trust_vc_vcir::check_crate(&invalid.krate).is_empty());

            let verification = verify::verify(&invalid, VerifyOptions::default());
            let outcome = verification.fns.get(&caller).unwrap();
            assert_eq!(outcome.verdict, Verdict::Refused);
            assert_eq!(outcome.tag.as_deref(), Some("unwind-diagnostic-source"));
            assert_eq!(
                outcome.sites,
                Some(SiteCounts {
                    proved: 0,
                    failed: 0
                })
            );
            let [Report::Refusal { span, tag, detail }] = verification.reports.as_slice() else {
                panic!(
                    "missing presentation must not emit a Failure: {:?}",
                    verification.reports
                )
            };
            assert_eq!(*span, call);
            assert_eq!(*tag, "unwind-diagnostic-source");
            assert_eq!(
                detail,
                "the conditional unwind callee has no original condition span"
            );
        },
    );
}
