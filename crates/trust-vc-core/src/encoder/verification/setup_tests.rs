// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::current_state_var_terms;
use ay_dpll::api::{Logic, Solver};
use std::collections::HashMap;

#[test]
fn test_current_state_var_terms_excludes_pre_state_suffix_entries() {
    let mut solver =
        Solver::try_new(Logic::All).expect("supported logic should construct a test solver");
    let current_x = solver.int_const(1);
    let current_y = solver.int_const(2);
    let pre_y = solver.int_const(3);

    let variables = HashMap::from([
        ("x".to_string(), current_x),
        ("y".to_string(), current_y),
        (format!("y{}", super::super::PRE_STATE_SUFFIX), pre_y),
    ]);

    let terms = current_state_var_terms(&variables);
    assert_eq!(
        terms.len(),
        2,
        "current-state helper must exclude pre-state shadow variables"
    );
    assert!(
        terms.contains(&current_x),
        "current-state helper must keep ordinary variables"
    );
    assert!(
        terms.contains(&current_y),
        "current-state helper must keep post-state variables"
    );
    assert!(
        !terms.contains(&pre_y),
        "current-state helper must drop __trust_vc_pre terms"
    );
}
