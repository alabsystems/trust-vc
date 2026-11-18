//! One fresh native compiler transaction for a generated whole program.
//!
//! This component returns observations only. It does not create
//! NativeOwnership, complete the original-to-shadow correspondence, or admit
//! a function. The original current TcX and canonical mode Rc stay on the
//! caller's stack while this independently initialized worker is joined.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_driver;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use rustc_data_structures::steal::Steal;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::{emitter::Emitter, DiagInner};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::middle::resolve::{ResolverAstLowering, ResolverGlobalCtxt};
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::util::Providers;
use rustc_session::config::Input;
use rustc_session::Session;
use rustc_span::hygiene::{AstPass, ExpnKind};
use rustc_span::source_map::SourceMap;
use rustc_span::FileName;

use super::program::{
    AdtId, AdtKind, AuxiliaryKind, EmittedProgram, FunctionId, GenericId, Program, Role, Site, Type,
};

mod allocations;
mod auxiliaries;
mod body_roles;
mod diagnostics;
mod source_file;

#[cfg(test)]
mod tests;

type ResolverProvider = for<'tcx> fn(
    TyCtxt<'tcx>,
    (),
) -> (
    &'tcx Steal<ResolverAstLowering<'tcx>>,
    &'tcx Steal<rustc_ast::Crate>,
    &'tcx ResolverGlobalCtxt,
);

/// Owned configuration data only. The production caller must bind the actual
/// original native invocation/options; an arbitrary argv is not source proof.
/// BackendCapable is the unchanged public driver route, never NoTrustEvidence.
pub(super) struct Recipe {
    pub(super) argv: Vec<String>,
    pub(super) source: PathBuf,
    pub(super) output: PathBuf,
    pub(super) effective_frontend: Option<usize>,
}

#[derive(Debug)]
pub(super) struct Observation {
    pub(super) compiler_returned_ok: bool,
    pub(super) expanded: bool,
    pub(super) analysis: bool,
    pub(super) typed_roots: BTreeSet<FunctionId>,
    pub(super) borrow_queries: BTreeMap<FunctionId, bool>,
    pub(super) typed_auxiliaries: BTreeSet<AuxiliaryKind>,
    pub(super) auxiliary_borrow_queries: BTreeMap<AuxiliaryKind, bool>,
    /// Issued role IDs checked against actual parser/HIR data; no Source admission.
    pub(super) checked_body_roles: BTreeSet<(Site, Role)>,
    pub(super) errors: Vec<String>,
    pub(super) refusal: Option<String>,
    #[cfg(test)]
    pub(super) full_source_byte_comparisons: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Correspondence {
    Declarations,
    OrdinaryBodies,
}

struct Expected {
    correspondence: Correspondence,
    program: Program,
    emitted: EmittedProgram,
    source: PathBuf,
    output: PathBuf,
    frontend: Option<usize>,
    source_byte_comparisons: AtomicUsize,
}

/// Exactly one worker for the entire program. No native compiler value or
/// original compiler reference is captured by the spawned closure or returned.
pub(super) fn observe(program: Program, recipe: Recipe) -> Result<Observation, String> {
    let emitted = program.emit()?;
    observe_prepared(program, recipe, emitted, Correspondence::Declarations)
}

// Test-only tampering exercises allocation/body/region rejection against real
// fresh compiler inputs. The ordinary entry has no raw-source callback.
#[cfg(test)]
fn observe_with_transform(
    program: Program,
    recipe: Recipe,
    transform: impl FnOnce(&mut EmittedProgram),
) -> Result<Observation, String> {
    let mut emitted = program.emit()?;
    transform(&mut emitted);
    observe_prepared(program, recipe, emitted, Correspondence::Declarations)
}

/// A strict ordinary-body transaction. Unsupported roles fail explicitly;
/// this is still not an original-source/native ownership result.
pub(super) fn observe_body_roles(program: Program, recipe: Recipe) -> Result<Observation, String> {
    let emitted = program.emit()?;
    observe_prepared(program, recipe, emitted, Correspondence::OrdinaryBodies)
}

#[cfg(test)]
fn observe_body_roles_with_transform(
    program: Program,
    recipe: Recipe,
    transform: impl FnOnce(&mut EmittedProgram),
) -> Result<Observation, String> {
    let mut emitted = program.emit()?;
    transform(&mut emitted);
    observe_prepared(program, recipe, emitted, Correspondence::OrdinaryBodies)
}

fn observe_prepared(
    program: Program,
    recipe: Recipe,
    emitted: EmittedProgram,
    correspondence: Correspondence,
) -> Result<Observation, String> {
    if program.builtin.is_some() {
        // The selected builtin adapter still needs its actual native CStore,
        // member signature and fresh-cohort checks. Never substitute a helper
        // by name, matching arity, a path/hash descriptor or a test crate.
        return Err("the fresh native builtin-cohort adapter is not materialized".into());
    }
    if !recipe.source.is_absolute()
        || !recipe.output.is_absolute()
        || recipe.source.parent() != Some(recipe.output.as_path())
    {
        return Err(
            "the generated native input and output need one explicit absolute owned directory"
                .into(),
        );
    }
    if recipe
        .output
        .canonicalize()
        .map_err(|error| error.to_string())?
        != recipe.output
    {
        return Err("the fresh native compiler directory is not its canonical owned path".into());
    }
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&recipe.source)
        .map_err(|e| e.to_string())?;
    file.write_all(emitted.source.as_bytes())
        .and_then(|_| file.sync_all())
        .map_err(|e| e.to_string())?;
    drop(file);
    let expected = Arc::new(Expected {
        correspondence,
        program,
        emitted,
        source: recipe.source.clone(),
        output: recipe.output.clone(),
        frontend: recipe.effective_frontend,
        source_byte_comparisons: AtomicUsize::new(0),
    });
    let worker = std::thread::Builder::new()
        .name("trust-vc-native-shadow".into())
        .spawn(move || run(expected, recipe))
        .map_err(|error| error.to_string())?;
    worker.join().map_err(|_| {
        "the fresh native shadow compiler panicked; no ownership result exists".to_owned()
    })?
}

fn run(expected: Arc<Expected>, recipe: Recipe) -> Result<Observation, String> {
    let errors = Arc::new(Mutex::new(Vec::new()));
    let mut callback = Run {
        expected,
        errors: Arc::clone(&errors),
        expanded: false,
        analysis: false,
        typed_roots: BTreeSet::new(),
        borrow_queries: BTreeMap::new(),
        typed_auxiliaries: BTreeSet::new(),
        auxiliary_borrow_queries: BTreeMap::new(),
        checked_body_roles: BTreeSet::new(),
        refusal: None,
    };
    let compiler = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&recipe.argv, &mut callback)
    });
    let errors = errors
        .lock()
        .map_err(|_| "native diagnostic capture was poisoned")?
        .clone();
    Ok(Observation {
        compiler_returned_ok: compiler.is_ok(),
        expanded: callback.expanded,
        analysis: callback.analysis,
        typed_roots: callback.typed_roots,
        borrow_queries: callback.borrow_queries,
        typed_auxiliaries: callback.typed_auxiliaries,
        auxiliary_borrow_queries: callback.auxiliary_borrow_queries,
        errors,
        checked_body_roles: callback.checked_body_roles,
        refusal: callback.refusal,
        #[cfg(test)]
        full_source_byte_comparisons: callback
            .expected
            .source_byte_comparisons
            .load(Ordering::Relaxed),
    })
}

struct Capture(Arc<Mutex<Vec<String>>>);
impl Emitter for Capture {
    fn emit_diagnostic(&mut self, diagnostic: DiagInner) {
        if diagnostic.is_error() {
            // Convert diagnostic data while its native context is live. No
            // native Span/Symbol/Diag/Ty crosses the compiler-thread boundary.
            self.0.lock().unwrap().push(
                diagnostic
                    .code
                    .map(|code| code.to_string())
                    .unwrap_or_else(|| format!("{:?}", diagnostic.messages)),
            );
        }
    }
    fn source_map(&self) -> Option<&SourceMap> {
        None
    }
}

#[derive(Default)]
struct State {
    original: Option<ResolverProvider>,
    expected: Option<Arc<Expected>>,
    functions: BTreeMap<FunctionId, LocalDefId>,
    adts: BTreeMap<AdtId, LocalDefId>,
    auxiliaries: BTreeMap<AuxiliaryKind, LocalDefId>,
    ast_calls: Vec<String>,
    call_allocations: BTreeMap<(Site, Role), allocations::Call>,
    body_allocations: Option<body_roles::Captured>,
    call_budget: usize,
    refusal: Option<String>,
    expansions: usize,
}

fn install(session: &Session, providers: &mut Providers) {
    session.with_trust_compiler_state::<State, _>(|state| {
        assert!(state.expected.is_some() && state.original.is_none());
        state.original = Some(providers.queries.resolver_for_lowering_raw);
    });
    providers.queries.resolver_for_lowering_raw = expanded;
}

fn expanded<'tcx>(
    tcx: TyCtxt<'tcx>,
    (): (),
) -> (
    &'tcx Steal<ResolverAstLowering<'tcx>>,
    &'tcx Steal<rustc_ast::Crate>,
    &'tcx ResolverGlobalCtxt,
) {
    let (original, expected) = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        (
            state.original.unwrap(),
            Arc::clone(state.expected.as_ref().unwrap()),
        )
    });
    let result = original(tcx, ());
    let checked = (|| {
        if tcx.dcx().has_errors().is_some()
            || tcx.sess.opts.jobs.frontend.map(|jobs| jobs.get()) != expected.frontend
        {
            return Err("the fresh native compiler changed its effective frontend mode or has expansion errors".to_owned());
        }
        let resolver = result.0.borrow();
        let krate = result.1.borrow();
        // The deliberately bounded raw diagnostic walk is test instrumentation,
        // never production call intake or an additional producer work grant.
        #[cfg(test)]
        {
            let ast_calls = diagnostics::ast_calls(tcx, &resolver, &krate);
            tcx.sess
                .with_trust_compiler_state::<State, _>(|state| state.ast_calls = ast_calls);
        }
        let mut functions = BTreeMap::new();
        let mut adts = BTreeMap::new();
        let mut auxiliaries = BTreeMap::new();
        let mut standard_import_expansion = None;
        let mut standard_externs = 0;
        let mut standard_globs = 0;
        // Anchor one complete byte comparison in an actual parser-allocated
        // authored item. The ordinary native StdImports pair is still checked
        // separately below; it never supplies an authored source allocation.
        let first = krate
            .items
            .iter()
            .find(|item| item.span.lo().0 != 0 || item.span.hi().0 != 0)
            .ok_or("the native parser published no authored source allocation")?;
        let source = tcx.sess.source_map().lookup_source_file(first.span.lo());
        let parsed_source = source_file::ParsedSource::new(
            &source,
            &expected.source,
            &expected.emitted.source,
            &expected.source_byte_comparisons,
        )?;
        for item in &krate.items {
            // The normal compiler injects exactly its std extern/prelude pair
            // at a dummy source position under one genuine StdImports pass.
            // Source text, a matching name or a foreign expansion is not a
            // substitute for this native provenance. No user root is skipped.
            let expansion = item.span.ctxt().outer_expn();
            if item.span.lo().0 == 0
                && item.span.hi().0 == 0
                && expansion.as_local().is_some()
                && matches!(
                    expansion.expn_data().kind,
                    ExpnKind::AstPass(AstPass::StdImports)
                )
            {
                if standard_import_expansion.is_some_and(|old| old != expansion) {
                    return Err("native standard imports came from multiple compiler passes".into());
                }
                standard_import_expansion = Some(expansion);
                match &item.kind {
                    rustc_ast::ItemKind::ExternCrate(None, ident) if ident.name == rustc_span::sym::std => standard_externs += 1,
                    rustc_ast::ItemKind::Use(tree) if matches!(tree.kind, rustc_ast::UseTreeKind::Glob(_)) => standard_globs += 1,
                    _ => return Err("the native standard-library pass published an unexpected auxiliary declaration".into()),
                }
                continue;
            }
            let (start, end) = parsed_source.range(tcx.sess.source_map(), item.span)?;
            let owner = resolver
                .owners
                .get(&item.id)
                .ok_or("the native parser/resolver did not publish its actual AST owner")?
                .def_id;
            match &item.kind {
                rustc_ast::ItemKind::Fn(_) => {
                    if let Some(kind) = expected.program.auxiliaries.iter().find_map(|auxiliary| {
                        expected
                            .emitted
                            .roles
                            .get(&(auxiliary.site, Role::Auxiliary))
                            .filter(|range| range.start == start && range.end == end)
                            .map(|_| auxiliary.kind)
                    }) {
                        if auxiliaries.insert(kind, owner).is_some() {
                            return Err(
                                "the compiler published an auxiliary allocation twice".into()
                            );
                        }
                        continue;
                    }
                    let id = expected
                        .program
                        .functions
                        .iter()
                        .find_map(|function| {
                            expected
                                .emitted
                                .roles
                                .get(&(function.site, Role::Function))
                                .filter(|range| range.start == start && range.end == end)
                                .map(|_| function.id)
                        })
                        .ok_or("a fresh native function has no exact generated declaration role")?;
                    if functions.insert(id, owner).is_some() {
                        return Err("the compiler published a generated function role twice".into());
                    }
                }
                rustc_ast::ItemKind::Enum(..) | rustc_ast::ItemKind::Struct(..) => {
                    let id = expected
                        .program
                        .adts
                        .iter()
                        .find_map(|adt| {
                            expected
                                .emitted
                                .roles
                                .get(&(adt.site, Role::Adt))
                                .filter(|range| range.start == start && range.end == end)
                                .map(|_| adt.id)
                        })
                        .ok_or("a fresh native ADT has no exact generated declaration role")?;
                    if adts.insert(id, owner).is_some() {
                        return Err("the compiler published a generated ADT role twice".into());
                    }
                }
                _ => {
                    return Err(
                        "the fresh native program contains an unplanned declaration kind".into(),
                    )
                }
            }
        }
        if standard_externs != 1 || standard_globs != 1 {
            return Err(
                "the fresh native compiler's standard import pair is incomplete or duplicated"
                    .into(),
            );
        }
        if functions.len() != expected.program.functions.len()
            || adts.len() != expected.program.adts.len()
            || auxiliaries.len() != expected.program.auxiliaries.len()
        {
            return Err("the fresh native compiler omitted a generated declaration role".into());
        }
        let mut captured_calls = allocations::capture(
            tcx,
            &resolver,
            &krate,
            &expected,
            &functions,
            &auxiliaries,
            &parsed_source,
        )?;
        let body_allocations = if expected.correspondence == Correspondence::OrdinaryBodies {
            let captured = body_roles::capture(
                tcx,
                &resolver,
                &krate,
                &expected,
                &functions,
                &adts,
                &parsed_source,
                captured_calls.remaining,
            )?;
            captured_calls.remaining = captured.remaining;
            Some(captured)
        } else {
            None
        };
        Ok((
            functions,
            adts,
            auxiliaries,
            captured_calls,
            body_allocations,
        ))
    })();
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        state.expansions += 1;
        match checked {
            Ok((functions, adts, auxiliaries, captured_calls, body_allocations)) => {
                state.functions = functions;
                state.adts = adts;
                state.auxiliaries = auxiliaries;
                state.call_allocations = captured_calls.calls;
                state.body_allocations = body_allocations;
                state.call_budget = captured_calls.remaining;
            }
            Err(error) => state.refusal = Some(error),
        }
    });
    result
}

struct Run {
    expected: Arc<Expected>,
    errors: Arc<Mutex<Vec<String>>>,
    expanded: bool,
    analysis: bool,
    typed_roots: BTreeSet<FunctionId>,
    borrow_queries: BTreeMap<FunctionId, bool>,
    typed_auxiliaries: BTreeSet<AuxiliaryKind>,
    auxiliary_borrow_queries: BTreeMap<AuxiliaryKind, bool>,
    checked_body_roles: BTreeSet<(Site, Role)>,
    refusal: Option<String>,
}
impl Callbacks for Run {
    fn config(&mut self, config: &mut Config) {
        // The compiler always reads the owned generated input and its existing
        // maintained private-output configuration. An incomplete recipe must
        // never read/recompile the original input or write its destinations.
        config.input = Input::File(self.expected.source.clone());
        if config.opts.incremental.is_some() {
            rustc_session::EarlyDiagCtxt::new(config.opts.error_format).early_fatal(
                "native ownership-shadow observation does not support incremental compiler state",
            );
        }
        crate::cargo_native::configure(config, &self.expected.output);
        if config.output_dir.as_ref() != Some(&self.expected.output) || config.output_file.is_some()
            || config.opts.output_types.len() != 2
            || config.opts.output_types.iter().any(|(_, output)| !matches!(output, Some(rustc_session::config::OutFileName::Real(path)) if path.starts_with(&self.expected.output))) {
            rustc_session::EarlyDiagCtxt::new(config.opts.error_format).early_fatal("the native shadow compiler retained an unrepresented output destination");
        }
        if config.override_queries.is_some()
            || config.track_state.is_some()
            || config.psess_created.is_some()
        {
            self.refusal = Some(
                "the fresh native entry already has an unrepresented callback/query configuration"
                    .into(),
            );
            return;
        }
        config.override_queries = Some(install);
        let expected = Arc::clone(&self.expected);
        config.track_state = Some(Box::new(move |session| {
            session.with_trust_compiler_state::<State, _>(|state| {
                assert!(state.expected.replace(Arc::clone(&expected)).is_none());
            })
        }));
        let errors = Arc::clone(&self.errors);
        config.psess_created = Some(Box::new(move |parse| {
            parse.dcx().set_emitter(Box::new(Capture(errors)))
        }));
    }

    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.expanded = true;
        if self.refusal.is_some() {
            return Compilation::Stop;
        }
        let same_transaction = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
            state
                .expected
                .as_ref()
                .is_some_and(|expected| Arc::ptr_eq(expected, &self.expected))
        });
        if !same_transaction {
            self.refusal =
                Some("the parser allocation map belongs to another live native transaction".into());
            return Compilation::Stop;
        }
        let (
            functions,
            adts,
            auxiliaries,
            call_allocations,
            body_allocations,
            mut call_budget,
            refusal,
            expansions,
        ) = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
            (
                std::mem::take(&mut state.functions),
                std::mem::take(&mut state.adts),
                std::mem::take(&mut state.auxiliaries),
                std::mem::take(&mut state.call_allocations),
                state.body_allocations.take(),
                std::mem::take(&mut state.call_budget),
                state.refusal.clone(),
                state.expansions,
            )
        });
        if let Some(error) = refusal {
            self.refusal = Some(error);
            return Compilation::Stop;
        }
        if expansions != 1 || functions.len() != self.expected.program.functions.len() {
            self.refusal = Some("native declaration publication did not close exactly once".into());
            return Compilation::Stop;
        }
        if let Err(error) = check_adts(tcx, &self.expected.program, &adts) {
            self.refusal = Some(error);
            return Compilation::Stop;
        }
        let mut declarations = BTreeMap::new();
        for (kind, owner) in &auxiliaries {
            match auxiliaries::check(tcx, *owner, *kind) {
                Ok(declaration) => {
                    declarations.insert(*kind, declaration);
                }
                Err(error) => {
                    self.refusal = Some(error);
                    return Compilation::Stop;
                }
            }
            self.typed_auxiliaries.insert(*kind);
        }
        for function in &self.expected.program.functions {
            let owner = functions[&function.id];
            if let Err(error) = check_signature(tcx, owner, function, &adts) {
                self.refusal = Some(error);
                return Compilation::Stop;
            }
            self.typed_roots.insert(function.id);
        }
        if let Err(error) = auxiliaries::check_calls(
            tcx,
            &self.expected,
            &functions,
            &adts,
            &auxiliaries,
            &declarations,
            &call_allocations,
            &mut call_budget,
        ) {
            self.refusal = Some(error);
            return Compilation::Stop;
        }
        if self.expected.correspondence == Correspondence::OrdinaryBodies {
            let Some(mut allocations) = body_allocations else {
                self.refusal =
                    Some("the native transaction omitted ordinary parser allocations".into());
                return Compilation::Stop;
            };
            // Continue the same native account after actual auxiliary checks;
            // never refill it from the earlier parser snapshot.
            allocations.remaining = call_budget;
            match body_roles::check(tcx, &self.expected, &functions, &adts, allocations) {
                Ok(roles) => self.checked_body_roles = roles,
                Err(error) => {
                    self.refusal = Some(error);
                    return Compilation::Stop;
                }
            }
        }
        // These are real checks of the actual fresh compiler's roots. They
        // still grant no original-source eligibility without the full source
        // correspondence, option/cohort and expression/control-flow joins.
        for (id, owner) in functions {
            self.borrow_queries
                .insert(id, tcx.mir_borrowck(owner).is_ok());
        }
        for (kind, owner) in auxiliaries {
            self.auxiliary_borrow_queries
                .insert(kind, tcx.mir_borrowck(owner).is_ok());
        }
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if tcx.dcx().has_errors().is_none() && self.refusal.is_none() {
            self.analysis = true;
        }
        Compilation::Stop
    }
}

fn check_signature<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    expected: &super::program::Function,
    adts: &BTreeMap<AdtId, LocalDefId>,
) -> Result<(), String> {
    let body = tcx.hir_body_owned_by(owner);
    let typeck = tcx.typeck(owner);
    if typeck.tainted_by_errors.is_some()
        || tcx.dcx().has_errors().is_some()
        || body.params.len() != expected.parameters.len()
    {
        return Err("the fresh native root has tainted or incomplete actual type checking".into());
    }
    let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
    if signature.safety().is_unsafe()
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
        || signature.inputs().len() != expected.parameters.len()
    {
        return Err("the fresh native root changed its actual function signature".into());
    }
    let generics = tcx.generics_of(owner);
    if generics.parent.is_some()
        || generics.own_params.len() != expected.regions.len() + expected.generics.len()
    {
        return Err("the fresh native root changed its generic frame".into());
    }
    for (index, parameter) in generics.own_params.iter().enumerate() {
        if if index < expected.regions.len() {
            !matches!(parameter.kind, ty::GenericParamDefKind::Lifetime)
        } else {
            !matches!(parameter.kind, ty::GenericParamDefKind::Type { .. })
        } {
            return Err("the fresh native root changed its lifetime/type binder kinds".into());
        }
    }
    for (actual, parameter) in signature.inputs().iter().zip(&expected.parameters) {
        compare_type(
            tcx,
            *actual,
            &parameter.ty,
            Frame {
                generics: &expected.generics,
                regions: expected.regions.len(),
            },
            adts,
        )?;
    }
    compare_type(
        tcx,
        signature.output(),
        &expected.result,
        Frame {
            generics: &expected.generics,
            regions: expected.regions.len(),
        },
        adts,
    )
}

fn check_adts(
    tcx: TyCtxt<'_>,
    program: &Program,
    adts: &BTreeMap<AdtId, LocalDefId>,
) -> Result<(), String> {
    for expected in &program.adts {
        let owner = adts[&expected.id];
        let actual = tcx.adt_def(owner);
        let generics = tcx.generics_of(owner);
        if (expected.kind == AdtKind::Enum && !actual.is_enum())
            || (expected.kind == AdtKind::Struct && !actual.is_struct())
            || generics.parent.is_some()
            || generics.own_params.len() != expected.generics.len()
            || generics
                .own_params
                .iter()
                .any(|parameter| !matches!(parameter.kind, ty::GenericParamDefKind::Type { .. }))
            || actual.variants().len() != expected.variants.len()
        {
            return Err(
                "the fresh native ADT changed its genuine kind, binder frame or variant shape"
                    .into(),
            );
        }
        for (actual, expected_variant) in actual.variants().iter().zip(&expected.variants) {
            if actual.fields.len() != expected_variant.fields.len() {
                return Err("the fresh native ADT changed a field declaration".into());
            }
            for (field, expected_field) in actual.fields.iter().zip(&expected_variant.fields) {
                let field_type = tcx.try_normalize_erasing_regions(
                    ty::TypingEnv::non_body_analysis(tcx, owner.to_def_id()),
                    tcx.type_of(field.did).instantiate_identity(),
                ).map_err(|_| "the actual generated field type cannot be normalized in its native declaration environment")?;
                compare_type(
                    tcx,
                    field_type,
                    &expected_field.ty,
                    Frame {
                        generics: &expected.generics,
                        regions: 0,
                    },
                    adts,
                )?;
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct Frame<'a> {
    generics: &'a [GenericId],
    regions: usize,
}
fn compare_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    actual: ty::Ty<'tcx>,
    expected: &Type,
    frame: Frame<'_>,
    adts: &BTreeMap<AdtId, LocalDefId>,
) -> Result<(), String> {
    let matches = match (actual.kind(), expected) {
        (ty::Tuple(types), Type::Unit) => types.is_empty(),
        (ty::Bool, Type::Bool) | (ty::Never, Type::Never) => true,
        (ty::Int(actual), Type::Signed(expected)) => {
            actual.name_str() == format!("{expected:?}").to_ascii_lowercase()
        }
        (ty::Uint(actual), Type::Unsigned(expected)) => {
            actual.name_str() == format!("{expected:?}").to_ascii_lowercase()
        }
        (ty::Param(parameter), Type::Parameter(expected)) => frame
            .generics
            .iter()
            .position(|id| id == expected)
            .is_some_and(|index| parameter.index as usize == frame.regions + index),
        (ty::Tuple(actual), Type::Tuple(expected)) => {
            if actual.len() != expected.len() {
                false
            } else {
                for (actual, expected) in actual.iter().zip(expected) {
                    compare_type(tcx, actual, expected, frame, adts)?;
                }
                true
            }
        }
        (ty::Adt(actual, arguments), Type::Adt(expected, types)) => {
            if actual.did().as_local() != adts.get(expected).copied()
                || arguments.len() != types.len()
            {
                false
            } else {
                for (actual, expected) in arguments.types().zip(types) {
                    compare_type(tcx, actual, expected, frame, adts)?;
                }
                true
            }
        }
        // References need the complete original/native region and alias frame
        // join. Do not treat erased lifetime names as equivalent permission.
        _ => false,
    };
    if matches {
        Ok(())
    } else {
        Err("the fresh native type differs from its structural program role (or needs an unimplemented native frame join)".into())
    }
}
