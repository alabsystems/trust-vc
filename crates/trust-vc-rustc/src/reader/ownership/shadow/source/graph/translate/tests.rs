//! Actual original-TcX/mode/availability controls for private source mapping.
//! These never emit a shadow, run its worker, or admit Source ownership.
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

extern crate rustc_driver;

use super::*;
use crate::reader::{self, modes, FnInfo, Instances, ReadOptions};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Directory(PathBuf);
impl Drop for Directory {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

type Inspect = for<'tcx> fn(TyCtxt<'tcx>);
struct Original {
    inspect: Inspect,
    ran: bool,
}
impl Callbacks for Original {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        (self.inspect)(tcx);
        assert!(tcx.dcx().has_errors().is_none());
        self.ran = true;
        Compilation::Stop
    }
}

fn native(source: &str, inspect: Inspect) {
    let directory = Directory(std::env::temp_dir().join(format!(
        "trust-vc-original-struct-map-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let original = directory.0.join("original.rs");
    std::fs::write(&original, format!(
        "#![feature(register_tool, never_type)]\n#![register_tool(verus)]\n#![allow(dead_code)]\n{source}\n"
    )).unwrap();
    let argv = vec![
        "original-struct-map-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=original_struct_map_control".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.0.to_str().unwrap().into(),
        original.to_str().unwrap().into(),
    ];
    let mut callback = Original {
        inspect,
        ran: false,
    };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&argv, &mut callback))
        .expect("the original source must complete its actual native analysis");
    assert!(callback.ran);
}

/// A private fixture context populated from this actual original native crate.
/// The declaration index supplies no import/SDK/ownership capability. Every
/// mode Rc below is produced by the complete ordinary checker in this Cx.
fn context<'tcx>(tcx: TyCtxt<'tcx>) -> Cx<'tcx> {
    let items = reader::verus_item_table(tcx);
    let (architecture, errors, refusals) = reader::architecture::collect(tcx, &items);
    assert!(errors.is_empty() && refusals.is_empty());
    let mut cx = Cx {
        tcx,
        architecture: architecture.architecture(),
        constants: reader::constants::Registry::collect(tcx),
        items,
        fns: HashMap::new(),
        legacy_functions: HashSet::new(),
        adts: HashMap::new(),
        projections: RefCell::new(HashMap::new()),
        projection_impls: RefCell::new(HashMap::new()),
        projection_type_work: Cell::new(0),
        source_opaque_nominals: HashSet::new(),
        imports: None,
        spec_definitions: trust_vc_vcir::CheckedSpecDefinitions::default(),
        local_variant_fields: None,
        enum_diagnostics: HashSet::new(),
        derived_clones: reader::derived_clones::Registry::default(),
        autospec: reader::autospec::Registry::default(),
        spans: RefCell::new(Vec::new()),
        explicit_returns: RefCell::new(HashSet::new()),
        native_ownership: RefCell::new(HashMap::new()),
        checked_modes: RefCell::new(HashMap::new()),
        ghost_tail_occurrences: RefCell::new(Vec::new()),
        opts: ReadOptions::default(),
        spec_methods: HashMap::new(),
        instances: RefCell::new(Instances::default()),
        impl_uses: RefCell::new(HashMap::new()),
        extra_deps: RefCell::new(HashMap::new()),
        dropped_calls: RefCell::new(HashMap::new()),
        bound_hides: RefCell::new(HashMap::new()),
        inherited_counts: RefCell::new(HashMap::new()),
    };
    let mut roots = Vec::new();
    for owner in tcx.hir_crate_items(()).owners() {
        let definition = owner.def_id;
        let attributes = cx.declaration_attrs(definition);
        if !attributes.verus_macro {
            continue;
        }
        assert!(!attributes.external && !attributes.external_body && !attributes.uninterp);
        assert!(attributes.unsupported.is_empty());
        match tcx.def_kind(definition) {
            DefKind::Fn => {
                assert_eq!(tcx.def_kind(tcx.local_parent(definition)), DefKind::Mod);
                cx.fns.insert(
                    definition.to_def_id(),
                    FnInfo {
                        id: trust_vc_vcir::FnId(cx.def_hash(definition.to_def_id())),
                        mode: attributes.mode.unwrap_or(Mode::Exec),
                    },
                );
                roots.push(definition);
            }
            DefKind::Struct | DefKind::Enum => {
                cx.adts.insert(
                    definition.to_def_id(),
                    trust_vc_vcir::AdtId(cx.def_hash(definition.to_def_id())),
                );
            }
            _ => {}
        }
    }
    assert!(!roots.is_empty());
    for root in roots {
        let checked = match modes::check_fn(&cx, root) {
            modes::ModeCheck::Clean(checked) => checked,
            result => panic!("the real original whole-body modes must complete: {result:?}"),
        };
        assert_eq!(checked.signature.body_owner, root);
        cx.checked_modes.borrow_mut().insert(root, Rc::new(checked));
    }
    assert!(cx.native_ownership.borrow().is_empty());
    cx
}

fn named(tcx: TyCtxt<'_>, name: &str) -> LocalDefId {
    tcx.hir_crate_items(())
        .owners()
        .map(|owner| owner.def_id)
        .find(|owner| {
            tcx.opt_item_name(owner.to_def_id())
                .is_some_and(|actual| actual.as_str() == name)
        })
        .unwrap()
}

fn mapped<'cx, 'tcx>(cx: &'cx Cx<'tcx>, root: LocalDefId) -> Mapped<'cx, 'tcx> {
    let graph = LiveGraph::collect(cx, &[root]).unwrap();
    assert!(Rc::ptr_eq(
        &graph.roots[0].source.checked,
        cx.checked_modes.borrow().get(&root).unwrap()
    ));
    let mapped = graph
        .translate()
        .unwrap_or_else(|reason| panic!("original source mapping: {reason}"));
    assert!(
        !mapped.unresolved.is_empty(),
        "structural success cannot admit ownership"
    );
    assert!(cx.native_ownership.borrow().is_empty());
    for origin in mapped.origins.values() {
        if let Origin::Place {
            source,
            native,
            environment,
            ..
        } = origin
        {
            let owner = source.hir_id.owner.def_id;
            assert!(
                matches!(cx.tcx.hir_node(source.hir_id), hir::Node::Expr(current)
                if std::ptr::eq(current, *source))
            );
            assert_eq!(*native, cx.tcx.typeck(owner).expr_ty(source));
            assert_eq!(*environment, ty::TypingEnv::post_analysis(cx.tcx, owner));
        }
    }
    mapped
}

fn body<'a>(mapped: &'a Mapped<'_, '_>, source: LocalDefId) -> &'a out::Expr {
    let id = mapped.functions[&source];
    &mapped
        .program
        .functions
        .iter()
        .find(|function| function.id == id)
        .unwrap()
        .body
}

fn tail(expression: &out::Expr) -> &out::Expr {
    match &expression.kind {
        out::ExprKind::Block {
            statements,
            tail: Some(value),
        } if statements.is_empty() => tail(value),
        _ => expression,
    }
}

#[test]
fn original_struct_literals_and_tuple_constructors_keep_actual_slots_and_written_order() {
    native(
        r#"
#[verus::internal(verus_macro)] struct Pair<A, B> { left: A, right: B }
#[verus::internal(verus_macro)] struct Tuple<A, B>(A, B);
#[verus::internal(verus_macro)] fn record(left: u8, right: u16) -> Pair<u8, u16> {
    Pair { right, left }
}
#[verus::internal(verus_macro)] fn tuple(left: u8, right: u16) -> Tuple<u8, u16> {
    Tuple(left, right)
}
"#,
        |tcx| {
            let cx = context(tcx);
            for (name, expected) in [("record", vec![1, 0]), ("tuple", vec![0, 1])] {
                let owner = named(tcx, name);
                let mapped = mapped(&cx, owner);
                let out::ExprKind::ConstructStruct { adt, types, fields } =
                    &tail(body(&mapped, owner)).kind
                else {
                    panic!("the actual source constructor must become a genuine struct constructor")
                };
                assert_eq!(
                    types,
                    &vec![
                        out::Type::Unsigned(out::Unsigned::U8),
                        out::Type::Unsigned(out::Unsigned::U16)
                    ]
                );
                assert_eq!(
                    fields.iter().map(|(slot, _)| *slot).collect::<Vec<_>>(),
                    expected
                );
                assert_eq!(
                    mapped
                        .program
                        .adts
                        .iter()
                        .find(|item| item.id == *adt)
                        .unwrap()
                        .kind,
                    out::AdtKind::Struct
                );
                let original_fields = &tcx
                    .adt_def(named(tcx, if name == "record" { "Pair" } else { "Tuple" }))
                    .non_enum_variant()
                    .fields;
                assert_eq!(original_fields.len(), fields.len());
            }
        },
    );
}

#[test]
fn original_generic_partial_moves_and_nested_field_assignment_use_real_place_origins() {
    native(
        r#"
#[verus::internal(verus_macro)] struct Pair<A, B> { left: A, right: B }
#[verus::internal(verus_macro)] fn partial<A, B>(value: Pair<A, B>) -> (A, B) {
    (value.left, value.right)
}
#[verus::internal(verus_macro)] fn nested(mut value: (Pair<u8, u16>, u8), replacement: u8) -> (u8, u16) {
    value.0.left = replacement;
    (value.0.left, value.0.right)
}
"#,
        |tcx| {
            let cx = context(tcx);
            let partial = named(tcx, "partial");
            let mapped_partial = mapped(&cx, partial);
            let out::ExprKind::Tuple(values) = &tail(body(&mapped_partial, partial)).kind else {
                panic!()
            };
            let slots = values
                .iter()
                .map(|value| match &value.kind {
                    out::ExprKind::StructField { field, types, .. } => {
                        assert_eq!(types.len(), 2);
                        assert!(types.iter().all(|ty| matches!(ty, out::Type::Parameter(_))));
                        *field
                    }
                    _ => panic!("the original generic reads must remain native struct places"),
                })
                .collect::<Vec<_>>();
            assert_eq!(slots, [0, 1]);
            assert_eq!(
                mapped_partial
                    .origins
                    .values()
                    .filter(|origin| matches!(origin, Origin::Place { .. }))
                    .count(),
                2
            );

            let nested = named(tcx, "nested");
            let mapped_nested = mapped(&cx, nested);
            let out::ExprKind::Block {
                statements,
                tail: Some(_),
            } = &body(&mapped_nested, nested).kind
            else {
                panic!()
            };
            let out::Statement::Expression(out::Expr {
                kind: out::ExprKind::AssignPlace { destination, .. },
                ..
            }) = &statements[0]
            else {
                panic!()
            };
            let out::ExprKind::StructField { base, field: 0, .. } = &destination.kind else {
                panic!()
            };
            assert!(matches!(
                base.kind,
                out::ExprKind::TupleField { field: 0, .. }
            ));
            assert!(
                mapped_nested
                    .origins
                    .values()
                    .filter(|origin| matches!(origin, Origin::Place { .. }))
                    .count()
                    >= 6
            );
        },
    );
}

#[test]
fn original_never_field_keeps_its_native_type_and_rejects_a_bool_substitution() {
    native(
        r#"
#[verus::internal(verus_macro)] struct Empty { value: ! }
#[verus::internal(verus_macro)] fn read(value: Empty) -> ! { value.value }
"#,
        |tcx| {
            let cx = context(tcx);
            let owner = named(tcx, "read");
            let mapped = mapped(&cx, owner);
            assert_eq!(mapped.program.functions[0].result, out::Type::Never);
            assert!(matches!(
                tail(body(&mapped, owner)).kind,
                out::ExprKind::StructField { field: 0, .. }
            ));
            assert_eq!(
                mapped.program.adts[0].variants[0].fields[0].ty,
                out::Type::Never
            );

            let graph = LiveGraph::collect(&cx, &[owner]).unwrap();
            let declaration = tcx.adt_def(named(tcx, "Empty"));
            let field = declaration.non_enum_variant().fields.iter().next().unwrap();
            let native = tcx
                .type_of(field.did)
                .instantiate_identity()
                .skip_normalization();
            let walk = Walk {
                graph: &graph,
                next_site: 0,
                next_local: 0,
                origins: BTreeMap::new(),
                functions: HashMap::new(),
                root_positions: HashMap::new(),
                locals: HashMap::new(),
                local_types: HashMap::new(),
                need_observer: false,
                uses: HashSet::new(),
                arguments: HashSet::new(),
                operations: HashSet::new(),
                adjustments: HashSet::new(),
            };
            walk.corresponding_type(&graph.roots[0], native, &out::Type::Never, 0)
                .unwrap();
            assert!(walk
                .corresponding_type(&graph.roots[0], native, &out::Type::Bool, 0)
                .is_err());
            assert!(cx.native_ownership.borrow().is_empty());
        },
    );
}

#[test]
fn original_struct_mapping_debits_the_retained_graph_for_exact_short_and_zero_work() {
    native(
        r#"
#[verus::internal(verus_macro)] struct Pair(u8, u16);
#[verus::internal(verus_macro)] fn fields(left: u8, right: u16, replacement: u8) -> (u8, u16) {
    let mut value = Pair(left, right);
    value.0 = replacement;
    (value.0, value.1)
}
"#,
        |tcx| {
            let cx = context(tcx);
            let owner = named(tcx, "fields");
            let baseline = LiveGraph::collect(&cx, &[owner]).unwrap();
            let initial = baseline.remaining_work.get();
            let success = baseline.translate().unwrap();
            let cost = initial - success.graph.remaining_work.get();
            assert!(cost > 1);
            let exact = LiveGraph::collect(&cx, &[owner]).unwrap();
            exact.remaining_work.set(cost);
            let success = exact.translate().unwrap();
            assert_eq!(success.graph.remaining_work.get(), 0);
            for remaining in [0, cost - 1] {
                let exhausted = LiveGraph::collect(&cx, &[owner]).unwrap();
                exhausted.remaining_work.set(remaining);
                let error = match exhausted.translate() {
                    Ok(_) => panic!("mapping must fail before exceeding its retained work ledger"),
                    Err(error) => error,
                };
                assert!(
                    error.contains("work") || error.contains("bound") || error.contains("ledger"),
                    "{error}"
                );
            }
            assert!(cx.native_ownership.borrow().is_empty());
        },
    );
}

#[test]
fn original_struct_updates_and_adjusted_reference_fields_remain_explicit_refusals() {
    native(
        r#"
#[verus::internal(verus_macro)] struct Pair { left: u8, right: u16 }
#[verus::internal(verus_macro)] fn update(value: Pair, left: u8) -> Pair { Pair { left, ..value } }
#[verus::internal(verus_macro)] fn adjusted(value: &Pair) -> u8 { value.left }
"#,
        |tcx| {
            let cx = context(tcx);
            for (name, expected) in [("update", "struct updates"), ("adjusted", "reference")] {
                let graph = LiveGraph::collect(&cx, &[named(tcx, name)]).unwrap();
                let error = match graph.translate() {
                    Ok(_) => panic!("unsupported original source cannot become a mapped program"),
                    Err(error) => error,
                };
                assert!(
                    error.contains(expected)
                        || (name == "adjusted"
                            && (error.contains("region") || error.contains("adjustment"))),
                    "{name}: {error}"
                );
            }
            assert!(cx.native_ownership.borrow().is_empty());
        },
    );
}
