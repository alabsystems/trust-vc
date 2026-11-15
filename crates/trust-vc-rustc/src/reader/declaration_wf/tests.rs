// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::declaration_policy::Recursion;
use super::graph::{self, Declaration, Graph, Type};

mod native_controls;

fn declaration(parameters: Vec<Recursion>, variants: Vec<Vec<Type>>) -> Declaration {
    Declaration {
        parameters,
        variants,
    }
}

fn nominal(node: usize) -> Type {
    Type::Nominal {
        node,
        arguments: vec![],
    }
}

fn function(input: Type, output: Type) -> Type {
    Type::SpecFunction {
        inputs: vec![input],
        output: Box::new(output),
    }
}

#[test]
fn function_input_polarity_requires_explicit_reject() {
    for policy in [
        Recursion::Reject,
        Recursion::RejectInGround,
        Recursion::Accept,
    ] {
        let graph = Graph {
            declarations: vec![declaration(
                vec![policy],
                vec![vec![function(Type::Parameter(0), Type::Base)]],
            )],
        };
        assert_eq!(graph::validate(&graph).is_ok(), policy == Recursion::Reject);
    }
}

#[test]
fn double_function_inputs_do_not_restore_strict_positivity() {
    let graph = Graph {
        declarations: vec![declaration(
            vec![Recursion::RejectInGround],
            vec![vec![function(
                function(Type::Parameter(0), Type::Base),
                Type::Base,
            )]],
        )],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn function_inputs_cannot_hide_a_recursive_datatype() {
    let graph = Graph {
        declarations: vec![declaration(
            vec![],
            vec![vec![], vec![function(nominal(0), Type::Base)]],
        )],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn positive_cycles_cannot_create_their_own_base_case() {
    let graph = Graph {
        declarations: vec![
            declaration(vec![], vec![vec![nominal(1)]]),
            declaration(vec![], vec![vec![nominal(0)]]),
        ],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn a_real_base_case_propagates_across_mutual_recursion() {
    let graph = Graph {
        declarations: vec![
            declaration(vec![], vec![vec![nominal(1)]]),
            declaration(vec![], vec![vec![nominal(0)], vec![]]),
        ],
    };
    assert!(graph::validate(&graph).is_ok());
}

#[test]
fn all_reachable_declarations_need_a_base_case() {
    let graph = Graph {
        declarations: vec![
            declaration(vec![], vec![vec![]]),
            declaration(vec![], vec![]),
        ],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn accept_parameters_cannot_supply_a_ground_variant() {
    for policy in [
        Recursion::Reject,
        Recursion::RejectInGround,
        Recursion::Accept,
    ] {
        let graph = Graph {
            declarations: vec![declaration(vec![policy], vec![vec![Type::Parameter(0)]])],
        };
        assert_eq!(graph::validate(&graph).is_ok(), policy != Recursion::Accept);
    }
}

#[test]
fn an_accepting_wrapper_can_supply_a_base_without_a_recursive_argument() {
    let graph = Graph {
        declarations: vec![
            declaration(
                vec![],
                vec![vec![Type::Nominal {
                    node: 1,
                    arguments: vec![nominal(0)],
                }]],
            ),
            declaration(vec![Recursion::Accept], vec![vec![]]),
        ],
    };
    assert!(graph::validate(&graph).is_ok());
}

#[test]
fn rejecting_wrapper_arguments_are_non_positive() {
    let graph = Graph {
        declarations: vec![
            declaration(
                vec![],
                vec![
                    vec![],
                    vec![Type::Nominal {
                        node: 1,
                        arguments: vec![nominal(0)],
                    }],
                ],
            ),
            declaration(vec![Recursion::Reject], vec![vec![]]),
        ],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn malformed_indices_and_arity_refuse() {
    for declarations in [
        vec![declaration(vec![], vec![vec![Type::Parameter(0)]])],
        vec![declaration(vec![], vec![vec![nominal(1)]])],
        vec![declaration(vec![Recursion::Reject], vec![vec![nominal(0)]])],
    ] {
        assert!(graph::validate(&Graph { declarations }).is_err());
    }
}

#[test]
fn tuple_and_decorations_preserve_base_case_requirements() {
    let graph = Graph {
        declarations: vec![declaration(
            vec![],
            vec![vec![Type::Product(vec![
                Type::Base,
                Type::Decorated(Box::new(nominal(0))),
            ])]],
        )],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn bounded_validation_refuses_excessive_type_depth() {
    let mut field = Type::Base;
    for _ in 0..66 {
        field = Type::Decorated(Box::new(field));
    }
    assert!(graph::validate(&Graph {
        declarations: vec![declaration(vec![], vec![vec![field]])]
    })
    .is_err());
}

fn imported(policy: Recursion, argument: Type) -> Type {
    Type::Imported {
        parameters: vec![policy],
        arguments: vec![argument],
    }
}

#[test]
fn imported_carriers_accept_concrete_founded_arguments() {
    for policy in [
        Recursion::Reject,
        Recursion::RejectInGround,
        Recursion::Accept,
    ] {
        assert!(graph::validate(&Graph {
            declarations: vec![declaration(
                vec![],
                vec![vec![imported(policy, Type::Base)]]
            )]
        })
        .is_ok());
    }
}

#[test]
fn imported_reject_keeps_recursive_arguments_non_positive_even_with_a_base() {
    for policy in [
        Recursion::Reject,
        Recursion::RejectInGround,
        Recursion::Accept,
    ] {
        let graph = Graph {
            declarations: vec![declaration(
                vec![],
                vec![vec![], vec![imported(policy, nominal(0))]],
            )],
        };
        assert_eq!(graph::validate(&graph).is_ok(), policy != Recursion::Reject);
    }
}

#[test]
fn only_imported_accept_can_found_a_recursive_argument_without_its_own_base() {
    for policy in [
        Recursion::Reject,
        Recursion::RejectInGround,
        Recursion::Accept,
    ] {
        let graph = Graph {
            declarations: vec![declaration(
                vec![],
                vec![vec![imported(policy, nominal(0))]],
            )],
        };
        assert_eq!(graph::validate(&graph).is_ok(), policy == Recursion::Accept);
    }
}

#[test]
fn imported_accept_never_restores_positive_polarity_in_a_function_input() {
    let graph = Graph {
        declarations: vec![declaration(
            vec![],
            vec![
                vec![],
                vec![function(
                    imported(Recursion::Accept, nominal(0)),
                    Type::Base,
                )],
            ],
        )],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn imported_policy_applies_to_local_formals_before_any_recursive_instance() {
    for owner in [
        Recursion::Reject,
        Recursion::RejectInGround,
        Recursion::Accept,
    ] {
        let graph = Graph {
            declarations: vec![declaration(
                vec![owner],
                vec![vec![imported(Recursion::Reject, Type::Parameter(0))]],
            )],
        };
        assert_eq!(graph::validate(&graph).is_ok(), owner == Recursion::Reject);
    }
}

#[test]
fn imported_arguments_preserve_dependencies_through_mutual_local_types() {
    let build = |policy| Graph {
        declarations: vec![
            declaration(vec![], vec![vec![imported(policy, nominal(1))]]),
            declaration(vec![], vec![vec![nominal(0)]]),
        ],
    };
    assert!(graph::validate(&build(Recursion::Accept)).is_ok());
    assert!(graph::validate(&build(Recursion::Reject)).is_err());
    assert!(graph::validate(&build(Recursion::RejectInGround)).is_err());
}

#[test]
fn imported_summary_never_supplies_a_missing_local_datatype_base() {
    let graph = Graph {
        declarations: vec![
            declaration(vec![], vec![vec![imported(Recursion::Accept, nominal(1))]]),
            declaration(vec![], vec![]),
        ],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn imported_policy_arity_and_size_are_checked_before_zip() {
    for parameters in [
        vec![],
        vec![Recursion::Accept; 2],
        vec![Recursion::Accept; 257],
    ] {
        assert!(graph::validate(&Graph {
            declarations: vec![declaration(
                vec![],
                vec![vec![Type::Imported {
                    parameters,
                    arguments: vec![Type::Base]
                }]]
            )]
        })
        .is_err());
    }
    let graph = Graph {
        declarations: vec![declaration(
            vec![],
            vec![vec![Type::Imported {
                parameters: vec![Recursion::Accept; 257],
                arguments: (0..257).map(|_| Type::Base).collect(),
            }]],
        )],
    };
    assert!(graph::validate(&graph).is_err());
}

#[test]
fn language_failures_have_exact_original_graph_owners() {
    let non_positive = Graph {
        declarations: vec![
            declaration(vec![], vec![vec![]]),
            declaration(
                vec![],
                vec![vec![], vec![imported(Recursion::Reject, nominal(1))]],
            ),
        ],
    };
    assert!(matches!(
        graph::validate(&non_positive),
        Err(graph::Failure::NonPositiveDatatype {
            owner: 1,
            target: 1
        })
    ));
    let parameter = Graph {
        declarations: vec![declaration(
            vec![Recursion::RejectInGround],
            vec![vec![imported(Recursion::Reject, Type::Parameter(0))]],
        )],
    };
    assert!(matches!(
        graph::validate(&parameter),
        Err(graph::Failure::NonPositiveParameter {
            owner: 0,
            parameter: 0
        })
    ));
    let no_base = Graph {
        declarations: vec![
            declaration(vec![], vec![vec![]]),
            declaration(
                vec![],
                vec![vec![imported(Recursion::RejectInGround, nominal(1))]],
            ),
        ],
    };
    assert!(matches!(graph::validate(&no_base),
        Err(graph::Failure::NoBase { owners }) if owners == vec![1]));
}

#[test]
fn no_base_preserves_all_owners_for_the_native_dependency_order() {
    let root_then_leaf = Graph {
        declarations: vec![
            declaration(vec![], vec![vec![nominal(1)]]),
            declaration(vec![], vec![vec![nominal(1)]]),
        ],
    };
    assert!(matches!(graph::validate(&root_then_leaf),
        Err(graph::Failure::NoBase { owners }) if owners == vec![0, 1]));
}

#[test]
fn unavailable_shape_and_resource_facts_are_not_language_failures() {
    let arity = Graph {
        declarations: vec![declaration(
            vec![],
            vec![vec![Type::Imported {
                parameters: vec![],
                arguments: vec![Type::Base],
            }]],
        )],
    };
    assert!(matches!(
        graph::validate(&arity),
        Err(graph::Failure::Unknown(_))
    ));
    let parameter = Graph {
        declarations: vec![declaration(vec![], vec![vec![Type::Parameter(0)]])],
    };
    assert!(matches!(
        graph::validate(&parameter),
        Err(graph::Failure::Unknown(_))
    ));
    let mut deep = Type::Base;
    for _ in 0..66 {
        deep = Type::Decorated(Box::new(deep));
    }
    let depth = Graph {
        declarations: vec![declaration(vec![], vec![vec![deep]])],
    };
    assert!(matches!(
        graph::validate(&depth),
        Err(graph::Failure::Unknown(_))
    ));
}
