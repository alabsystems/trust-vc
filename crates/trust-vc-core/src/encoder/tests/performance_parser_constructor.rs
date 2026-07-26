//! Performance proofs for `AstExpressionParser::new`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The parser constructor pre-seeds width metadata, collection metadata, and
//! map-domain tracking before expression encoding starts. Those passes walk the
//! declared context once, so setup should stay linear in the relevant context
//! size.

use super::*;

/// Seeding `term_widths` from scalar variables should stay O(V): one
/// `var_types` lookup and one HashMap insert per width-tracked variable.
#[test]
fn test_ast_expression_parser_new_scalar_width_seed_scaling_linear() {
    assert_linear_parser_constructor_scaling(
        ScalingCase {
            small: 40,
            large: 160,
            iterations: 500,
            small_expected: ParserExpectations::new(40, 0, 0, false),
            large_expected: ParserExpectations::new(160, 0, 0, false),
            label: "scalar width seeding",
            axis: "V",
            complexity_note: "Scalar width precomputation should stay O(V).",
        },
        build_scalar_fixture,
    );
}

/// In all-`MathInt` contexts, the constructor still walks every declared
/// variable even though no BitVec widths are seeded. That scan plus
/// `use_int_arithmetic` detection should stay O(V), not regress to O(V²).
#[test]
fn test_ast_expression_parser_new_math_int_context_scaling_linear() {
    assert_linear_parser_constructor_scaling(
        ScalingCase {
            small: 60,
            large: 240,
            iterations: 500,
            small_expected: ParserExpectations::new(0, 0, 0, true),
            large_expected: ParserExpectations::new(0, 0, 0, true),
            label: "MathInt context setup",
            axis: "V",
            complexity_note: "All-Int constructor setup should stay O(V).",
        },
        build_math_int_fixture,
    );
}

/// Map-heavy contexts seed three constructor-owned tables at once:
/// `collection_meta_by_term`, `domain_terms`, and pointer-width entries for
/// collection lengths. With one domain term per Map variable, that setup
/// should stay O(M), not O(M²).
#[test]
fn test_ast_expression_parser_new_map_metadata_scaling_linear() {
    assert_linear_parser_constructor_scaling(
        ScalingCase {
            small: 20,
            large: 80,
            iterations: 300,
            small_expected: ParserExpectations::new(20, 20, 20, false),
            large_expected: ParserExpectations::new(80, 80, 80, false),
            label: "map metadata seeding",
            axis: "M",
            complexity_note: "Map-domain and collection-metadata setup should stay O(M).",
        },
        build_map_fixture,
    );
}

/// Mixed collection families still route through the same constructor loops:
/// classify kind, attach the pre-declared length term, and recover map-domain
/// terms where applicable. That mixed metadata population should remain O(C).
#[test]
fn test_ast_expression_parser_new_mixed_collection_metadata_scaling_linear() {
    assert_linear_parser_constructor_scaling(
        ScalingCase {
            small: 24,
            large: 96,
            iterations: 250,
            small_expected: ParserExpectations::new(24, 24, count_map_entries(24), false),
            large_expected: ParserExpectations::new(96, 96, count_map_entries(96), false),
            label: "mixed collection setup",
            axis: "C",
            complexity_note: "Collection-kind and length metadata seeding should stay O(C).",
        },
        build_mixed_collection_fixture,
    );
}

#[derive(Clone, Copy)]
struct ParserExpectations {
    term_widths: usize,
    collection_meta: usize,
    domain_terms: usize,
    use_int_arithmetic: bool,
}

impl ParserExpectations {
    const fn new(
        term_widths: usize,
        collection_meta: usize,
        domain_terms: usize,
        use_int_arithmetic: bool,
    ) -> Self {
        Self {
            term_widths,
            collection_meta,
            domain_terms,
            use_int_arithmetic,
        }
    }
}

struct ParserFixture {
    solver: ay_dpll::api::Solver,
    variables: std::collections::HashMap<String, ay_dpll::api::Term>,
    collection_lengths: std::collections::HashMap<String, ay_dpll::api::Term>,
    var_types: std::collections::HashMap<String, crate::ir::TrustVcType>,
    functions: std::collections::HashMap<String, ay_dpll::api::FuncDecl>,
}

struct ScalingCase {
    small: usize,
    large: usize,
    iterations: usize,
    small_expected: ParserExpectations,
    large_expected: ParserExpectations,
    label: &'static str,
    axis: &'static str,
    complexity_note: &'static str,
}

fn assert_linear_parser_constructor_scaling(
    case: ScalingCase,
    build_fixture: impl Fn(usize) -> ParserFixture,
) {
    let small_fixture = std::cell::RefCell::new(build_fixture(case.small));
    let large_fixture = std::cell::RefCell::new(build_fixture(case.large));

    let t_small = measure_median(
        || {
            let mut fixture = small_fixture.borrow_mut();
            time_ast_expression_parser_new(&mut fixture, case.small_expected, case.iterations)
        },
        3,
    );
    let t_large = measure_median(
        || {
            let mut fixture = large_fixture.borrow_mut();
            time_ast_expression_parser_new(&mut fixture, case.large_expected, case.iterations)
        },
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = case.large as f64 / case.small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "AstExpressionParser::new {} appears quadratic: \
         T({}={})={}us, T({}={})={}us, ratio={:.1}x, normalized={:.1}x. \
         {}",
        case.label,
        case.axis,
        case.small,
        t_small,
        case.axis,
        case.large,
        t_large,
        ratio,
        normalized,
        case.complexity_note,
    );
}

fn time_ast_expression_parser_new(
    fixture: &mut ParserFixture,
    expected: ParserExpectations,
    iterations: usize,
) -> u128 {
    let start = std::time::Instant::now();

    for _ in 0..iterations {
        let parser = AstExpressionParser::new(
            &mut fixture.solver,
            &fixture.variables,
            &mut fixture.collection_lengths,
            &fixture.var_types,
            &fixture.functions,
        );

        assert_eq!(
            parser.term_widths.len(),
            expected.term_widths,
            "constructor should seed the expected number of term widths"
        );
        assert_eq!(
            parser.collection_meta_by_term.len(),
            expected.collection_meta,
            "constructor should seed the expected number of collection metadata entries"
        );
        assert_eq!(
            parser.domain_terms.len(),
            expected.domain_terms,
            "constructor should seed the expected number of map domain terms"
        );
        assert_eq!(
            parser.use_int_arithmetic, expected.use_int_arithmetic,
            "constructor should classify the arithmetic mode deterministically"
        );

        std::hint::black_box((
            parser.term_widths.len(),
            parser.collection_meta_by_term.len(),
            parser.domain_terms.len(),
            parser.use_int_arithmetic,
        ));
    }

    start.elapsed().as_micros()
}

fn build_scalar_fixture(n_vars: usize) -> ParserFixture {
    let mut fixture = ParserFixture::new();

    for i in 0..n_vars {
        let name = format!("scalar_{i}");
        let ty = if i % 2 == 0 {
            crate::ir::TrustVcType::Int { width: 32 }
        } else {
            crate::ir::TrustVcType::Uint { width: 64 }
        };
        fixture.add_variable(name, ty);
    }

    fixture
}

fn build_math_int_fixture(n_vars: usize) -> ParserFixture {
    let mut fixture = ParserFixture::new();

    for i in 0..n_vars {
        fixture.add_variable(format!("math_{i}"), crate::ir::TrustVcType::MathInt);
    }

    fixture
}

fn build_map_fixture(n_maps: usize) -> ParserFixture {
    let mut fixture = ParserFixture::new();

    for i in 0..n_maps {
        fixture.add_collection(
            format!("map_{i}"),
            crate::ir::TrustVcType::Map(
                Box::new(crate::ir::TrustVcType::Uint { width: 32 }),
                Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            ),
        );
    }

    fixture
}

fn build_mixed_collection_fixture(n_collections: usize) -> ParserFixture {
    let mut fixture = ParserFixture::new();

    for i in 0..n_collections {
        let name = format!("collection_{i}");
        let ty = match i % 4 {
            0 => crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
            1 => crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Uint { width: 32 })),
            2 => crate::ir::TrustVcType::Map(
                Box::new(crate::ir::TrustVcType::Uint { width: 16 }),
                Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            ),
            _ => crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Bool)),
        };
        fixture.add_collection(name, ty);
    }

    fixture
}

fn count_map_entries(n_collections: usize) -> usize {
    (0..n_collections).filter(|i| i % 4 == 2).count()
}

impl ParserFixture {
    fn new() -> Self {
        Self {
            solver: ay_dpll::api::Solver::try_new(ay_dpll::api::Logic::All).expect("solver"),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn add_variable(&mut self, name: String, ty: crate::ir::TrustVcType) {
        let sort = crate::encoder::types::sort_for_type(&ty);
        let term = self.solver.declare_const(&name, sort);
        self.variables.insert(name.clone(), term);
        self.var_types.insert(name, ty);
    }

    fn add_collection(&mut self, name: String, ty: crate::ir::TrustVcType) {
        let sort = crate::encoder::types::sort_for_type(&ty);
        let term = self.solver.declare_const(&name, sort);
        self.variables.insert(name.clone(), term);
        self.var_types.insert(name.clone(), ty.clone());

        let len_name = format!("__trust_vc_len_{}", name);
        let len_term = self.solver.declare_const(
            &len_name,
            ay_dpll::api::Sort::bitvec(crate::ir::pointer_width()),
        );
        self.collection_lengths.insert(name.clone(), len_term);

        if let crate::ir::TrustVcType::Map(key_ty, _) = ty {
            let dom_name = format!("{}_dom", name);
            let dom_sort = ay_dpll::api::Sort::Array(Box::new(ay_dpll::api::ArraySort {
                index_sort: crate::encoder::types::sort_for_type(&key_ty),
                element_sort: ay_dpll::api::Sort::Bool,
            }));
            let dom_term = self.solver.declare_const(&dom_name, dom_sort);
            self.variables.insert(dom_name, dom_term);
        }
    }
}
