// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Every original body and every ordinary AY result must meet the exact oracle.
use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::term::Term;
use trust_vc_vcir::vcgen::{CheckKind, QueryGroup};

pub(super) fn require(source: VcCrate, expected: &[bool]) {
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{errors:?}");
    let result = vcgen::generate(&source);
    assert_eq!(result.fns.len(), source.fns.len());
    for function in &source.fns {
        assert_eq!(function.role, FnRole::Item);
        assert!(function.attrs.instance.is_none() && !function.attrs.external_body);
        let Some(FnVcs::Checks(checks)) = result.get(function.id) else {
            panic!("every original body must be supported: {result:?}");
        };
        let caller = function.id == id();
        assert_eq!(
            checks.len(),
            if caller {
                expected.len()
            } else {
                function.ensures.len()
            }
        );
        for (index, check) in checks.iter().enumerate() {
            assert!(!check.approximate && !check.order_unknown);
            assert_eq!(check.group, QueryGroup::Body);
            if caller {
                assert!(matches!(check.kind, CheckKind::Assert { .. }));
                assert!(!matches!(check.query.goal, Term::Bool(_)));
                assert_eq!(check.site, SiteId(index as u32));
            } else {
                assert_eq!(
                    check.kind,
                    CheckKind::Postcondition {
                        exit: span(),
                        clause: index
                    }
                );
                assert_eq!(check.site, SiteId(9));
            }
            let answer = check_detailed(&check.query, "typed field ownership", &Limits::default());
            let prove = !caller || expected[index];
            assert!(
                matches!(
                    (&answer.verdict, prove),
                    (Verdict::Proved { .. }, true) | (Verdict::Refuted { .. }, false)
                ),
                "function={:?} check={index} expected_proved={prove} goal={:?} answer={answer:?} query={:#?}", function.id, check.query.goal, check.query
            );
        }
    }
}
