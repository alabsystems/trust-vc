//! The reader: Verus items read out of rustc's HIR and type-check results,
//! and lowered into VcIR.
//!
//! It runs after `rustc_hir_analysis::check_crate` (every body type-checked)
//! and before borrow checking, the same point at which Verus reads a crate.
//! It never touches THIR or MIR.
//!
//! What it recognizes, and how:
//!
//! * Verus markers (`requires`, `assert_`, `spec_eq`, `SpecAdd::spec_add`, the
//!   `int` type, ...) by the `DefId` of the definition that carries the
//!   matching `verus::` diagnostic item ([`crate::verus_items`]). A callee is
//!   resolved through the type-check results, never by name.
//! * Verus items by the `#[verus::internal(verus_macro)]` attribute the
//!   `verus!` macro puts on everything it expands; modes and other
//!   directives by their `verus::internal` / `verifier::` attributes
//!   ([`attrs`]).
//!
//! Before a function is lowered, its modes are checked the way Verus's mode
//! checker checks them ([`modes`]). A function with a mode error is read
//! only for the errors of earlier phases, keeps its signature for the calls
//! of other functions, and is never verified.
//!
//! What it produces ([`CrateRead`]):
//!
//! * a [`VcCrate`] with one `FnDecl` per function it could read completely;
//! * a span table: `SpanId(i)` in the VcIR is `spans[i]`;
//! * one [`FnRecord`] per function: read, rejected by a Verus rule, refused
//!   with a tag, deferred to the borrow checker, or external;
//! * the Verus errors it found ([`UserError`]), each tagged with the Verus
//!   [`Phase`] that reports it.
//!
//! Anything outside the fragment it knows is refused with a tag
//! ([`Refusal`]); nothing is dropped or approximated.

mod architecture;
mod attr_walk;
pub mod attrs;
mod body;
mod constants;
mod cycles;
mod datatypes;
mod declaration_factory;
pub(crate) mod declaration_facts;
mod declaration_fields;
mod declaration_headers;
mod declaration_modes;
mod declaration_native;
mod declaration_policy;
pub mod declaration_staging;
mod declaration_types;
mod declaration_wf;
mod derived_clones;
mod enum_diagnostics;
mod function_identity;
pub(crate) mod function_identity_observer;
mod function_identity_projection;
mod function_identity_resolution;
mod ghost_tail_agreement;
mod imports;
mod local_variant_fields;
mod modes;
mod ownership;
mod recursive_types;
mod termination;
mod ty;
mod vtrans;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self as mty, TyCtxt};
use rustc_span::{FileName, Span};

use trust_vc_vcir::{
    AdtDecl, AdtId, AdtKind, DefHash, FieldDecl, FnId, Mode, SpanId, VariantDecl, VcCrate,
};

use crate::messages::{self, Phase};
use crate::verus_items::VerusItem;
use attrs::VerusAttr;

/// Something the reader does not handle. Reported as
/// `trust-vc refused: <tag>: <detail>` at `span`.
#[derive(Debug, Clone)]
pub struct Refusal {
    /// Lowercase words joined by dashes.
    pub tag: &'static str,
    /// What exactly was not handled.
    pub detail: String,
    /// Where.
    pub span: Span,
}

impl Refusal {
    pub(crate) fn new(tag: &'static str, detail: impl Into<String>, span: Span) -> Self {
        Self {
            tag,
            detail: detail.into(),
            span,
        }
    }
}

/// An error Verus itself reports for this program, with Verus's text.
#[derive(Debug, Clone)]
pub struct UserError {
    /// The Verus pass that reports it.
    pub phase: Phase,
    /// Primary span.
    pub span: Span,
    /// The message.
    pub message: String,
    /// Label on the primary span, if any.
    pub primary_label: Option<String>,
    /// Labels on other spans.
    pub labels: Vec<(Span, String)>,
    /// A help line, if any.
    pub help: Option<String>,
    /// The function whose checking reports it. Phases after building VIR
    /// report only their first error, in Verus's function order
    /// ([`CrateRead::verus_order`]).
    pub function: Option<LocalDefId>,
}

impl UserError {
    pub(crate) fn new(phase: Phase, span: Span, message: impl Into<String>) -> Self {
        Self {
            phase,
            span,
            message: message.into(),
            primary_label: None,
            labels: Vec::new(),
            help: None,
            function: None,
        }
    }
}

/// What the reader did with one function.
#[derive(Debug, Clone)]
pub enum FnStatus {
    /// Lowered completely; its `FnDecl` is in the crate.
    Read(FnId),
    /// Rejected by a Verus rule the reader checks; the error is in
    /// [`CrateRead::errors`].
    Rejected,
    /// Refused.
    Refused(Refusal),
    /// Holds an exec assignment to an immutable local (at this span), which
    /// rustc's borrow checker reports in the erase run; Verus's lifetime
    /// check stops before verification then. Its `FnDecl` is in the crate,
    /// for the VcIR checker only: it is never verified.
    Deferred(Span),
    /// Not a Verus item.
    External,
}

/// One function's entry.
#[derive(Debug, Clone)]
pub struct FnRecord {
    /// The definition.
    pub def_id: LocalDefId,
    /// `tcx.def_path_str`.
    pub def_path: String,
    /// `DefKind`, as text.
    pub kind: String,
    /// What happened.
    pub status: FnStatus,
}

/// Options from the command line that change what the reader reports.
#[derive(Debug, Clone, Copy, Default)]
pub struct ReadOptions {
    /// `-V new-mut-ref`: mutable references have opaque logical identity.
    /// Executable storage additionally requires native availability/resolution.
    pub new_mut_ref: bool,
    /// `--no-external-by-default`: items outside `verus!` are verified too.
    pub no_external_by_default: bool,
    /// `-V no-bv-simplify`: retain original BV expression occurrences.
    pub no_bv_simplify: bool,
}

/// Everything the reader produced for one crate.
#[derive(Debug)]
pub struct CrateRead {
    /// The actual reader invocation policy, retained with this immutable read.
    pub(crate) read_options: ReadOptions,
    /// The functions and data types read completely.
    pub krate: VcCrate,
    /// Separate equations admitted only by the live native library join.
    pub(crate) spec_definitions: trust_vc_vcir::CheckedSpecDefinitions,
    /// `SpanId(i)` is `spans[i]`.
    pub spans: Vec<Span>,
    /// Spans of `Return` statements that come from a `return` expression.
    /// The other returns are the end of a body; Verus labels the two
    /// differently when a postcondition fails there.
    pub explicit_returns: HashSet<SpanId>,
    /// One entry per function.
    pub fns: Vec<FnRecord>,
    /// Refusals of items that are not functions.
    pub item_refusals: Vec<Refusal>,
    /// Refusals that only verification needs: the functions were read
    /// completely but the VC generator cannot use them as read. They stand
    /// unless Verus rejects the crate first.
    pub verify_refusals: Vec<Refusal>,
    /// Refusals of items that cannot produce a Verus error while VIR is
    /// built. They stand unless a Verus error from that first phase rejects
    /// the crate, since Verus stops there whatever the items hold.
    pub pending_item_refusals: Vec<Refusal>,
    /// Verus errors, from every phase the reader checks.
    pub errors: Vec<UserError>,
    /// Verus's warnings from its well-formedness check, which it reports
    /// once that check passes.
    pub warnings: Vec<UserError>,
    /// The function each VcIR function id stands for.
    pub fn_defs: HashMap<FnId, LocalDefId>,
    /// Position of each function in the order Verus checks functions; see
    /// [`CrateRead::verus_order`].
    order: HashMap<LocalDefId, usize>,
    /// The modules that hold a Verus function.
    pub fn_modules: HashSet<LocalDefId>,
    /// Original typeck roots whose tracked values require native
    /// borrow checking before any verification result may be published.
    pub(crate) native_ownership: HashSet<LocalDefId>,
    /// Closed ghost-only components from this exact native read invocation.
    /// They are not ownership permission without the private live client join.
    pub(crate) ghost_ownership: HashMap<LocalDefId, ownership::ghost_only::GhostOnly>,
}

impl CrateRead {
    /// The rustc span of a VcIR span id.
    #[must_use]
    pub fn span(&self, id: SpanId) -> Option<Span> {
        self.spans.get(id.0 as usize).copied()
    }

    /// Where `function` comes in the order Verus checks functions after
    /// building VIR (`vir/src/ast_sort.rs`, `sort_krate`): grouped by module,
    /// deeper modules before their parents, modules of one depth in crate
    /// order and the functions of one module in source order. Unknown
    /// functions come last.
    #[must_use]
    pub fn verus_order(&self, function: Option<LocalDefId>) -> usize {
        function
            .and_then(|f| self.order.get(&f).copied())
            .unwrap_or(usize::MAX)
    }

    /// Every refusal, item-level and function-level, except
    /// [`Self::pending_item_refusals`].
    pub fn refusals(&self) -> impl Iterator<Item = &Refusal> {
        self.item_refusals
            .iter()
            .chain(self.fns.iter().filter_map(|f| match &f.status {
                FnStatus::Refused(r) => Some(r),
                _ => None,
            }))
    }
}

/// A Verus function known to the crate before any body is lowered, so calls
/// can refer to functions defined later.
#[derive(Debug, Clone, Copy)]
pub(crate) struct FnInfo {
    pub id: FnId,
    pub mode: Mode,
}

/// The tag of a refusal for a type Verus does not translate
/// ([`vtrans`]).
pub(crate) const TAG_VERUS_TYPE: &str = "verus-type";

/// The tag of a refusal for a type Verus translates and its
/// well-formedness check rejects ([`Cx::verus_wf_problem`]).
pub(crate) const TAG_VERUS_WF: &str = "verus-wf";

/// The name prefix `verus!` gives the specification method it splits off a
/// trait method declaration without a body: `fn f(..) requires ..;` becomes
/// `fn VERUS_SPEC__f(..) { requires(..); no_method_body() }` and a bare
/// `fn f(..);` (`builtin_macros/src/syntax_trait.rs`).
pub(crate) const VERUS_SPEC: &str = "VERUS_SPEC__";

/// The native declaration specified by a trait's generated companion.
/// This locates a pair only; callers separately decide its permitted use.
fn trait_spec_declaration(tcx: TyCtxt<'_>, spec: LocalDefId) -> Option<LocalDefId> {
    if tcx.def_kind(spec) != DefKind::AssocFn {
        return None;
    }
    let trait_id = tcx.local_parent(spec);
    if tcx.def_kind(trait_id) != DefKind::Trait {
        return None;
    }
    let name = tcx.item_name(spec.to_def_id());
    let target = name.as_str().strip_prefix(VERUS_SPEC)?;
    tcx.associated_items(trait_id)
        .in_definition_order()
        .find(|item| {
            matches!(item.kind, mty::AssocKind::Fn { .. })
                && item.name().as_str() == target
                && item.def_id != spec.to_def_id()
        })
        .and_then(|item| item.def_id.as_local())
        .filter(|decl| tcx.local_parent(*decl) == trait_id)
}

/// Diagnostic identity for an original item and its macro-cloned companion.
/// Equal names or a shared whole-macro callsite do not identify a source item.
/// This does not register a body, change classification, or grant visibility.
fn external_trait_source(tcx: TyCtxt<'_>, item: LocalDefId) -> LocalDefId {
    let Some(decl) = trait_spec_declaration(tcx, item) else {
        return item;
    };
    let (Some(spec_span), Some(decl_span)) = (
        tcx.def_ident_span(item.to_def_id()),
        tcx.def_ident_span(decl.to_def_id()),
    ) else {
        return item;
    };
    if spec_span.is_dummy()
        || decl_span.is_dummy()
        || spec_span.lo() >= spec_span.hi()
        || decl_span.lo() >= decl_span.hi()
    {
        return item;
    }
    let source_map = tcx.sess.source_map();
    let spec_file = source_map.lookup_source_file(spec_span.lo());
    let decl_file = source_map.lookup_source_file(decl_span.lo());
    if !matches!(spec_file.name, FileName::Real(_))
        || spec_file.stable_id != decl_file.stable_id
        || !spec_file.contains(spec_span.hi())
        || !decl_file.contains(decl_span.hi())
        || spec_file.original_relative_byte_pos(spec_span.lo())
            != decl_file.original_relative_byte_pos(decl_span.lo())
        || spec_file.original_relative_byte_pos(spec_span.hi())
            != decl_file.original_relative_byte_pos(decl_span.hi())
    {
        return item;
    }
    decl
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ExternalItemDiagnostic {
    Trait,
    TraitImpl,
}

/// Upper bound on the instances ([`Cx::instance`]) of one crate.
const MAX_INSTANCES: usize = 512;

/// Generic functions at concrete type arguments that calls asked for, and
/// the ones still to be read.
#[derive(Default)]
pub(crate) struct Instances<'tcx> {
    ids: HashMap<(DefId, mty::GenericArgs<'tcx>), FnId>,
    queue: Vec<(LocalDefId, mty::GenericArgs<'tcx>, FnId)>,
}

/// State shared by every function's lowering.
pub(crate) struct Cx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    /// Source-selected complete word-size contexts, never the host ABI.
    architecture: trust_vc_vcir::bitvector::Architecture,
    /// Real Rust constants and their checked local verification proxies.
    constants: constants::Registry,
    /// Every `verus::` diagnostic item in the crate graph, by definition.
    items: HashMap<DefId, VerusItem>,
    /// Verus functions of this crate.
    pub fns: HashMap<DefId, FnInfo>,
    /// Structs of this crate that VcIR represents.
    adts: HashMap<DefId, AdtId>,
    /// Original opaque source identities installed by a borrowed, current
    /// Keep capability. Membership only denies representation operations.
    source_opaque_nominals: HashSet<DefId>,
    /// Only a sealed current-client declaration packet populates this index.
    /// The ordinary product entry point has no implicit library authority.
    imports: Option<imports::Registry<'tcx>>,
    spec_definitions: trust_vc_vcir::CheckedSpecDefinitions,
    local_variant_fields: Option<local_variant_fields::Local<'tcx>>,
    enum_diagnostics: HashSet<DefId>,
    derived_clones: derived_clones::Registry,
    /// The span table.
    spans: RefCell<Vec<Span>>,
    /// See [`CrateRead::explicit_returns`].
    explicit_returns: RefCell<HashSet<SpanId>>,
    /// See [`CrateRead::native_ownership`]. Eligibility is established from
    /// clean modes and a body that needs no ownership erasure.
    native_ownership: RefCell<HashMap<LocalDefId, ownership::NativeOwnership>>,
    /// Completed mode facts stay in this exact compiler context, including
    /// their original generic body when instances are lowered later.
    checked_modes: RefCell<HashMap<LocalDefId, std::rc::Rc<modes::CheckedModes<'tcx>>>>,
    ghost_tail_occurrences: RefCell<Vec<modes::ExpectedGhostTail>>,
    pub opts: ReadOptions,
    /// The specification method (`VERUS_SPEC__f`) of each trait method
    /// declaration `f` that has one.
    pub spec_methods: HashMap<LocalDefId, LocalDefId>,
    /// See [`Instances`].
    instances: RefCell<Instances<'tcx>>,
    /// For each function, the trait implementations that satisfy the bounds
    /// of the functions it calls at concrete types.
    pub impl_uses: RefCell<HashMap<FnId, std::collections::BTreeMap<cycles::Item, bool>>>,
    /// The functions each function names with `extra_dependency`, which
    /// Verus's call graph has as calls.
    pub extra_deps: RefCell<HashMap<FnId, Vec<FnId>>>,
    /// The functions each function calls in values it discards, which VcIR
    /// drops and Verus's call graph has.
    pub dropped_calls: RefCell<HashMap<FnId, Vec<FnId>>>,
    /// For each function, the spec definitions it uses where it lacks
    /// their trait bounds, which it therefore may not see
    /// ([`cycles::unmet_bound`]).
    pub bound_hides:
        RefCell<HashMap<FnId, std::collections::BTreeMap<FnId, trust_vc_vcir::DefOrder>>>,
    /// For each method implementing a trait method, how many of its
    /// `requires`, `ensures` and `recommends` clauses (the leading ones) it
    /// inherits from the declaration.
    pub inherited_counts: RefCell<HashMap<FnId, (usize, usize, usize, bool)>>,
}

impl<'tcx> Cx<'tcx> {
    fn declaration_attrs(&self, def: LocalDefId) -> attrs::ItemAttrs {
        self.constants.item_attrs(self.tcx, def)
    }

    /// The Verus item a definition is, if any.
    pub(crate) fn verus_item(&self, def_id: DefId) -> Option<VerusItem> {
        self.items.get(&def_id).copied()
    }

    /// The VcIR id of a struct this crate defines, if VcIR represents it.
    pub(crate) fn adt_id(&self, def_id: DefId) -> Option<AdtId> {
        self.adts.get(&def_id).copied()
    }

    fn imported_nominal(&self, def_id: DefId) -> Option<AdtId> {
        self.imports.as_ref()?.nominal(self.tcx, def_id)
    }

    fn source_opaque_nominal(&self, def_id: DefId) -> bool {
        self.source_opaque_nominals.contains(&def_id)
    }

    /// Only type-argument occurrences are inspected. A source capability
    /// excludes every other datatype declaration from this reader; this
    /// query never inspects a nongeneric wrapper's private field language.
    fn mentions_source_opaque(&self, ty: mty::Ty<'tcx>) -> bool {
        ty.walk().any(|argument| {
            argument.as_type().is_some_and(
                |ty| matches!(ty.kind(), mty::Adt(adt, _) if self.source_opaque_nominal(adt.did())),
            )
        })
    }

    fn imported_function(&self, def_id: DefId) -> Option<(FnId, usize)> {
        self.imports.as_ref()?.function(self.tcx, def_id)
    }

    fn imported_seq_len(&self, def_id: DefId) -> bool {
        self.imports
            .as_ref()
            .is_some_and(|imports| imports.seq_len(self.tcx, def_id))
    }

    fn imported_seq_index(&self, def_id: DefId) -> bool {
        self.imports
            .as_ref()
            .is_some_and(|imports| imports.seq_index(self.tcx, def_id))
    }

    fn imported_nominal_policy(&self, def_id: DefId) -> Option<imports::NominalPolicy<'_>> {
        self.imports.as_ref()?.nominal_policy(self.tcx, def_id)
    }

    fn imported_wf_requirement(&self, requirement: &declaration_wf::BuiltinRequirement) -> bool {
        self.imports
            .as_ref()
            .is_some_and(|imports| imports.covers_wf_requirement(self.tcx, requirement))
    }

    /// Add a span to the table.
    pub(crate) fn span_id(&self, span: Span) -> SpanId {
        let mut spans = self.spans.borrow_mut();
        let id = u32::try_from(spans.len()).unwrap_or(u32::MAX);
        spans.push(span);
        SpanId(id)
    }

    /// The rustc span of a span id.
    pub(crate) fn span_of(&self, id: SpanId) -> Option<Span> {
        self.spans.borrow().get(id.0 as usize).copied()
    }

    /// Record that the `Return` at `span` comes from a `return` expression.
    pub(crate) fn mark_explicit_return(&self, span: SpanId) {
        self.explicit_returns.borrow_mut().insert(span);
    }

    /// The stable hash of a definition's path.
    pub(crate) fn def_hash(&self, def_id: DefId) -> DefHash {
        let (hi, lo) = self.tcx.def_path_hash(def_id).0.split();
        DefHash::new(hi.as_u64(), lo.as_u64())
    }

    /// The id of the Verus function `def_id` of this crate at the concrete
    /// type arguments `args` ([`trust_vc_vcir::FnRole::Instance`]); it is
    /// read after every function of the crate. `None` for a function that
    /// is not a Verus function of this crate.
    pub(crate) fn instance(&self, def_id: DefId, args: mty::GenericArgs<'tcx>) -> Option<FnId> {
        use std::hash::{Hash, Hasher};
        let local = def_id.as_local()?;
        self.fns.get(&def_id)?;
        let mut instances = self.instances.borrow_mut();
        if let Some(id) = instances.ids.get(&(def_id, args)) {
            return Some(*id);
        }
        // The path's hash, mixed with the arguments as rustc prints them;
        // that text names the arguments exactly within one compilation.
        let (hi, lo) = self.tcx.def_path_hash(def_id).0.split();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        format!("{args:?}").hash(&mut hasher);
        let mix = hasher.finish();
        let id = FnId(DefHash::new(
            hi.as_u64() ^ mix,
            lo.as_u64().rotate_left(17) ^ mix,
        ));
        instances.ids.insert((def_id, args), id);
        instances.queue.push((local, args, id));
        Some(id)
    }

    /// The next instance to read.
    fn next_instance(&self) -> Option<(LocalDefId, mty::GenericArgs<'tcx>, FnId)> {
        self.instances.borrow_mut().queue.pop()
    }

    /// Every instance, with its generic function and type arguments.
    fn instance_sources(&self) -> HashMap<FnId, (LocalDefId, mty::GenericArgs<'tcx>)> {
        self.instances
            .borrow()
            .ids
            .iter()
            .filter_map(|((def_id, args), id)| def_id.as_local().map(|local| (*id, (local, *args))))
            .collect()
    }
}

/// Every `verus::` diagnostic item visible to this crate, by definition.
fn verus_item_table(tcx: TyCtxt<'_>) -> HashMap<DefId, VerusItem> {
    let mut table = HashMap::new();
    for (name, def_id) in &tcx.all_diagnostic_items(()).name_to_id {
        if let Some(item) = VerusItem::from_name(name.as_str()) {
            table.insert(*def_id, item);
        }
    }
    table
}

/// Did the crate graph load `verus_builtin`? rustc loads an `--extern` crate
/// only when the program names it, and Verus refuses to run without it
/// (`verifier.rs`, `construct_vir_crate`, which looks for the
/// `erased_ghost_value` item).
pub fn builtin_loaded(tcx: TyCtxt<'_>) -> bool {
    tcx.all_diagnostic_items(())
        .name_to_id
        .keys()
        .any(|name| name.as_str() == "verus::verus_builtin::erased_ghost_value")
}

/// Does Verus ignore `def_id` as external (`rust_verify/src/external.rs`)?
/// It does when the item, or an item or module around it, is
/// `#[verifier::external]`, and when an item around it is `external_body`:
/// the items nested inside an `external_body` function are ignored, while
/// the function itself is not.
fn is_external(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let mut current = Some(def_id);
    while let Some(id) = current {
        let hir_id = tcx.local_def_id_to_hir_id(id);
        let attrs = attrs::item_attrs(tcx.hir_attrs(hir_id));
        let body_fn = matches!(tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn);
        if attrs.external || (id != def_id && body_fn && attrs.external_body) {
            return true;
        }
        current = tcx.opt_local_parent(id);
    }
    false
}

/// Is `def_id` an item nested in a body (a function's, a closure's, a
/// constant's, at any depth, through modules too) with `verus!` code around
/// it or in it?
///
/// Verus's lifetime check borrow-checks every checked function against the
/// whole crate, where each such item exists. The erase run compiles the crate
/// with ghost code erased: the bodies of proof and spec functions (external
/// or not), proof blocks, ghost initializers, and every item nested there.
/// An impl nested in an erased body is in Verus's crate and not in the erase
/// run's; an `impl Drop` there makes a move out of the type's fields an
/// ownership error in every function under Verus, which the erase run never
/// reports.
fn nested_in_verus_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let mut in_body = false;
    let mut verus = false;
    let mut current = Some(def_id);
    while let Some(id) = current {
        if id != def_id && !matches!(tcx.def_kind(id), DefKind::Mod) {
            in_body = true;
        }
        let hir_id = tcx.local_def_id_to_hir_id(id);
        if attrs::item_attrs(tcx.hir_attrs(hir_id)).verus_macro {
            verus = true;
        }
        current = tcx.opt_local_parent(id);
    }
    in_body && verus
}

/// Does Verus warn that `attr` has no effect on an item it ignores because
/// of an item around it? It does for every Verus attribute but a few
/// markers (`attributes.rs`, `get_external_attrs`: `external_body`,
/// `verify`, a mode, the `external_*_specification`s, and any other
/// Verus-specific attribute, the helper function of a `reveal` included).
/// Of the markers the reader knows, only `verus_macro` and `external` are
/// silent; an unknown attribute counts as warned about.
fn warned_when_ignored(attr: &VerusAttr) -> bool {
    !matches!(attr, VerusAttr::VerusMacro | VerusAttr::External)
}

/// The spans of the `reveal`/`hide` helper functions whose type checking
/// failed.
///
/// `reveal(path)` expands to a helper function whose body mentions `path`.
/// Verus replaces those bodies with `()` before type checking
/// (`rust_verify/src/hir_hide_reveal_rewrite.rs`) and resolves `path` from
/// name resolution alone, so a path whose type arguments cannot be inferred
/// (`A::<_>::f`, `<A<_> as Tr<_>>::f`, a `broadcast use` of a generic lemma)
/// is fine under Verus and a type error here. Call this after type checking
/// reported errors, to tell those errors from errors Verus would report too.
pub fn reveal_helpers_with_type_errors(tcx: TyCtxt<'_>) -> Vec<Span> {
    let mut spans = Vec::new();
    for owner in tcx.hir_crate_items(()).owners() {
        let def_id = owner.def_id;
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let hir_id = tcx.local_def_id_to_hir_id(def_id);
        if !attrs::item_attrs(tcx.hir_attrs(hir_id)).reveal_fn {
            continue;
        }
        if tcx.typeck(def_id).tainted_by_errors.is_some() {
            spans.push(tcx.def_span(def_id));
        }
    }
    spans
}

/// Read the whole crate.
pub fn read_crate(tcx: TyCtxt<'_>, opts: ReadOptions) -> CrateRead {
    read_with_imports(tcx, opts, None)
}

fn read_with_imports<'tcx>(
    tcx: TyCtxt<'tcx>,
    opts: ReadOptions,
    imports: Option<imports::Registry<'tcx>>,
) -> CrateRead {
    read_with_context(tcx, opts, imports, None)
}

/// A selection made from an original, live native dependency graph. The
/// staging finalizer authenticates every language item before supplying this
/// context; ordinary reads continue to use their complete native crate.
struct SpecReadContext<'facts, 'tcx> {
    owners: HashSet<LocalDefId>,
    items: HashMap<DefId, VerusItem>,
    source_nominals: Option<&'facts declaration_staging::SourceNominals<'facts, 'tcx>>,
}

fn read_with_context<'tcx>(
    tcx: TyCtxt<'tcx>,
    opts: ReadOptions,
    imports: Option<imports::Registry<'tcx>>,
    spec: Option<&SpecReadContext<'_, 'tcx>>,
) -> CrateRead {
    let items = spec.map_or_else(|| verus_item_table(tcx), |scope| scope.items.clone());
    let (global_sizes, global_errors, global_refusals) = architecture::collect(tcx, &items);
    let mut cx = Cx {
        tcx,
        architecture: global_sizes.architecture(),
        constants: constants::Registry::collect(tcx),
        items,
        fns: HashMap::new(),
        adts: HashMap::new(),
        source_opaque_nominals: HashSet::new(),
        imports,
        spec_definitions: trust_vc_vcir::CheckedSpecDefinitions::default(),
        local_variant_fields: None,
        enum_diagnostics: HashSet::new(),
        derived_clones: if spec.is_none() {
            derived_clones::Registry::collect(tcx, opts.no_external_by_default)
        } else {
            derived_clones::Registry::default()
        },
        spans: RefCell::new(Vec::new()),
        explicit_returns: RefCell::new(HashSet::new()),
        native_ownership: RefCell::new(HashMap::new()),
        checked_modes: RefCell::new(HashMap::new()),
        ghost_tail_occurrences: RefCell::new(Vec::new()),
        opts,
        spec_methods: HashMap::new(),
        instances: RefCell::new(Instances::default()),
        impl_uses: RefCell::new(HashMap::new()),
        extra_deps: RefCell::new(HashMap::new()),
        dropped_calls: RefCell::new(HashMap::new()),
        bound_hides: RefCell::new(HashMap::new()),
        inherited_counts: RefCell::new(HashMap::new()),
    };
    let mut krate = VcCrate::new(tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string());
    krate.pointer_width = u32::try_from(tcx.data_layout.pointer_size().bits()).unwrap_or(64);
    // The physical rustc ABI is not a proof restriction. Without a separately
    // checked source architecture directive Verus establishes both cases.
    krate.architecture = cx.architecture;

    let mut fns = Vec::new();
    let mut item_refusals = global_refusals;
    let mut pending_item_refusals = Vec::new();
    let mut structs = Vec::new();
    let mut errors = global_errors;
    let mut external_item_diagnostics = HashSet::new();
    // Verus's well-formedness warnings about function bodies.
    let mut fn_warnings: Vec<UserError> = Vec::new();
    // The `VERUS_SPEC__f` methods of traits, matched to their declarations
    // once every item is known.
    let mut spec_candidates = Vec::new();
    // Functions outside `verus!` read under `--no-external-by-default`.
    let mut outside_fns = HashSet::new();
    // Native recursion directives consumed in the declaration pass create a
    // later WF obligation even when no imported type occurs in the fields.
    let mut pending_recursion = HashSet::new();
    // The traits and trait implementations the reader reads.
    let mut read_items = Vec::new();
    let mut pending_enum_diagnostics = Vec::new();

    if let Some(nominals) = spec.and_then(|scope| scope.source_nominals) {
        if let Err(reason) = nominals.install(&mut cx, &mut krate) {
            item_refusals.push(Refusal::new(
                "source-opaque-context",
                reason,
                tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
            ));
        }
    }

    // First pass: classify every item and register the functions and datatypes
    // that other items may refer to.
    for owner in tcx.hir_crate_items(()).owners() {
        let def_id = owner.def_id;
        if cx.source_opaque_nominal(def_id.to_def_id()) {
            continue;
        }
        if spec.is_some_and(|scope| !scope.owners.contains(&def_id)) {
            continue;
        }
        if spec.is_some_and(|scope| scope.source_nominals.is_some())
            && !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
        {
            item_refusals.push(Refusal::new(
                "source-opaque-context",
                "an opaque source read permits only functions and its one checked carrier",
                tcx.def_span(def_id),
            ));
            continue;
        }
        if global_sizes.consumes(tcx, def_id) {
            continue;
        }
        let hir_id = tcx.local_def_id_to_hir_id(def_id);
        // Consuming native recursion directives creates an obligation below;
        // it grants no WF permission during this classification pass.
        let consumed_nominal = matches!(tcx.def_kind(def_id), DefKind::Struct)
            && cx.declaration_attrs(def_id).verus_macro
            && !is_external(tcx, def_id)
            && matches!(
                declaration_policy::local_directives::has_candidate(tcx, def_id.to_def_id()),
                Ok(true)
            );
        let native_policy =
            consumed_nominal.then(|| declaration_policy::check(tcx, def_id.to_def_id()));
        let native_directives = native_policy.as_ref().and_then(|policy| {
            declaration_policy::local_directives::capture(tcx, def_id.to_def_id(), policy).ok()
        });
        let ordinary_attributes = native_directives
            .as_ref()
            .and_then(|directives| directives.remaining(tcx, def_id.to_def_id()))
            .unwrap_or_else(|| tcx.hir_attrs(hir_id).to_vec());
        if native_directives
            .as_ref()
            .is_some_and(|directives| directives.has_directives(tcx))
        {
            pending_recursion.insert(def_id);
        }
        let own_attrs: Vec<_> = attrs::verus_attrs(&ordinary_attributes)
            .into_iter()
            .filter(|(attr, _)| !cx.constants.accepts_attribute(def_id, attr))
            .collect();
        let item_attrs = if native_directives.is_some() {
            attrs::item_attrs(&ordinary_attributes)
        } else {
            cx.declaration_attrs(def_id)
        };
        let span = tcx.def_span(def_id);
        // Where `external.rs` reports a problem with the item: all of it.
        let item_span = tcx.hir_span_with_body(hir_id);
        let kind = tcx.def_kind(def_id);
        // `#[verifier::external]` on an item or on anything around it (a
        // module, an impl) excludes it (`rust_verify/src/external.rs`).
        let external = is_external(tcx, def_id);
        // Under `--no-external-by-default` Verus reads items outside
        // `verus!` too. The reader reads their functions only for the errors
        // Verus reports while building VIR; they are refused otherwise.
        let loose = opts.no_external_by_default;
        let native_constant = kind == DefKind::AssocConst && cx.constants.mode(def_id).is_some();
        let derived_source = cx.derived_clones.source(def_id);
        let outside = !item_attrs.verus_macro && !native_constant && derived_source.is_none();
        let verus =
            (item_attrs.verus_macro || native_constant || derived_source.is_some() || loose)
                && !external;
        if verus && item_attrs.broadcast_forall && !matches!(kind, DefKind::Fn | DefKind::AssocFn) {
            item_refusals.push(Refusal::new(
                "broadcast-contract",
                "a broadcast marker on an item other than a function",
                span,
            ));
            continue;
        }
        // An impl nested in a body of Verus code, whatever the body's mode
        // and whether or not it is external: the erase run may not have it
        // where Verus's lifetime check does ([`nested_in_verus_body`]).
        if matches!(kind, DefKind::Impl { .. }) && nested_in_verus_body(tcx, def_id) {
            item_refusals.push(Refusal::new(
                "nested-impl",
                "an impl nested inside a body",
                span,
            ));
            continue;
        }
        // Verus also reads items outside `verus!` that carry Verus
        // attributes (`verify`, `external_body`, a mode, ...); the reader
        // only reads what `verus!` produced, so those are refused. The loop
        // settings only matter to the functions inside such an item, which
        // read them there (`attrs::loop_settings`).
        if outside && !item_attrs.reveal_fn {
            if let Some((attr, attr_span)) = own_attrs.iter().find(|(attr, _)| {
                !matches!(attr, VerusAttr::External) && !attrs::is_loop_setting(attr)
            }) {
                item_refusals.push(Refusal::new(
                    "outside-verus-macro",
                    format!("{attr:?} on an item outside verus!"),
                    *attr_span,
                ));
                continue;
            }
        }
        // An item Verus ignores because of an item around it, which asks to
        // be verified or trusted: Verus warns that the attribute has no
        // effect (`external.rs`, `emit_errors_warnings_for_ignored_attrs`).
        if external && !item_attrs.external {
            if let Some((attr, attr_span)) =
                own_attrs.iter().find(|(attr, _)| warned_when_ignored(attr))
            {
                item_refusals.push(Refusal::new(
                    "ignored-attribute",
                    format!("{attr:?} on an item inside an external or external_body item"),
                    *attr_span,
                ));
                continue;
            }
        }
        // `external.rs`: `external_body` belongs on a function, a
        // datatype or a constant.
        if item_attrs.external_body && def_id != rustc_hir::def_id::CRATE_DEF_ID {
            let parent_kind = tcx.opt_local_parent(def_id).map(|p| tcx.def_kind(p));
            let applicable = match kind {
                DefKind::Fn
                | DefKind::AssocFn
                | DefKind::Struct
                | DefKind::Enum
                | DefKind::Union
                | DefKind::Const => true,
                DefKind::AssocConst => parent_kind != Some(DefKind::Trait),
                _ => false,
            };
            if !applicable {
                errors.push(UserError::new(
                    Phase::RustToVir,
                    item_span,
                    messages::EXTERNAL_BODY_ITEM,
                ));
            }
        }
        // `external.rs`: an item of a trait Verus reads cannot be external.
        if item_attrs.external
            && matches!(
                kind,
                DefKind::AssocFn | DefKind::AssocTy | DefKind::AssocConst
            )
            && tcx.def_kind(tcx.local_parent(def_id)) == DefKind::Trait
            && !is_external(tcx, tcx.local_parent(def_id))
            && (loose
                || attrs::item_attrs(
                    tcx.hir_attrs(tcx.local_def_id_to_hir_id(tcx.local_parent(def_id))),
                )
                .verus_macro)
        {
            let source = external_trait_source(tcx, def_id);
            if external_item_diagnostics.insert((source, ExternalItemDiagnostic::Trait)) {
                errors.push(UserError::new(
                    Phase::RustToVir,
                    tcx.hir_span_with_body(tcx.local_def_id_to_hir_id(source)),
                    messages::traits::EXTERNAL_TRAIT_ITEM,
                ));
            }
        }
        // `external.rs`: one item of a trait implementation Verus reads
        // cannot be external.
        if item_attrs.external
            && matches!(kind, DefKind::AssocFn)
            && matches!(
                tcx.def_kind(tcx.local_parent(def_id)),
                DefKind::Impl { of_trait: true }
            )
            && !is_external(tcx, tcx.local_parent(def_id))
            && attrs::item_attrs(
                tcx.hir_attrs(tcx.local_def_id_to_hir_id(tcx.local_parent(def_id))),
            )
            .verus_macro
        {
            if external_item_diagnostics.insert((def_id, ExternalItemDiagnostic::TraitImpl)) {
                errors.push(UserError::new(
                    Phase::RustToVir,
                    item_span,
                    messages::traits::EXTERNAL_IMPL_ITEM,
                ));
            }
        }
        let enum_diagnostic = if own_attrs
            .iter()
            .any(|(attribute, _)| matches!(attribute, VerusAttr::GetFieldManyVariants))
        {
            match enum_diagnostics::prepare(tcx, def_id) {
                Ok(pending) => {
                    pending_enum_diagnostics.push(pending);
                    true
                }
                Err(reason) => {
                    item_refusals.push(Refusal::new("enum-diagnostic", reason, item_span));
                    continue;
                }
            }
        } else {
            false
        };
        // An item marked external that also asks for something else
        // (`external_fn_specification`, ...) is an error Verus reports.
        if item_attrs.external {
            if let Some((attr, attr_span)) = own_attrs.iter().find(|(attr, _)| {
                !matches!(
                    attr,
                    VerusAttr::External
                        | VerusAttr::VerusMacro
                        | VerusAttr::Mode(_)
                        | VerusAttr::Visibility { .. }
                ) && !(enum_diagnostic && matches!(attr, VerusAttr::GetFieldManyVariants))
            }) {
                item_refusals.push(Refusal::new(
                    "attribute",
                    format!("{attr:?} on an external item"),
                    *attr_span,
                ));
                continue;
            }
        }
        // A derived trait impl carries no `verus!` marker of its own;
        // Verus reads it with the attributes of its type.
        if matches!(kind, DefKind::Impl { of_trait: true })
            && tcx.is_automatically_derived(def_id.to_def_id())
            && !cx.derived_clones.implementation(def_id)
        {
            if let Some(refusal) = derived_impl_problem(tcx, def_id, loose) {
                item_refusals.push(refusal);
                continue;
            }
        }
        // Verus reads the recursive-types attributes on a generic parameter
        // as well as on the item (`rust_to_vir_base.rs`,
        // `check_generics_bounds_main`); the reader reads neither.
        if verus {
            let param_attr = tcx.hir_get_generics(def_id).and_then(|generics| {
                generics.params.iter().find_map(|param| {
                    let ordinary = native_directives
                        .as_ref()
                        .and_then(|directives| directives.remaining(tcx, param.def_id.to_def_id()))
                        .unwrap_or_else(|| tcx.hir_attrs(param.hir_id).to_vec());
                    attrs::verus_attrs(&ordinary).into_iter().next()
                })
            });
            if let Some((attr, attr_span)) = param_attr {
                item_refusals.push(Refusal::new(
                    "attribute",
                    format!("{attr:?} on a generic parameter"),
                    attr_span,
                ));
            }
        }
        match kind {
            DefKind::Fn | DefKind::AssocFn | DefKind::AssocConst
                if matches!(kind, DefKind::Fn | DefKind::AssocFn)
                    || cx.constants.mode(def_id).is_some() =>
            {
                if item_attrs.reveal_fn {
                    // The helper function of a `reveal`/`hide`; read as part
                    // of that statement.
                    continue;
                }
                // A trait's specification method is part of the
                // declaration it specifies, not a function of its own.
                if verus
                    && kind == DefKind::AssocFn
                    && tcx.def_kind(tcx.local_parent(def_id)) == DefKind::Trait
                    && tcx
                        .item_name(def_id.to_def_id())
                        .as_str()
                        .starts_with(VERUS_SPEC)
                {
                    spec_candidates.push(def_id);
                    continue;
                }
                let original = cx.constants.real(def_id).unwrap_or(def_id);
                let def_path = tcx.def_path_str(original.to_def_id());
                let record = |status| FnRecord {
                    def_id,
                    def_path: def_path.clone(),
                    kind: format!("{:?}", tcx.def_kind(original)),
                    status,
                };
                if !verus {
                    fns.push(record(FnStatus::External));
                    continue;
                }
                if outside {
                    pending_item_refusals.push(Refusal::new(
                        "external-by-default",
                        format!(
                            "`{def_path}` is outside verus! and --no-external-by-default is set"
                        ),
                        span,
                    ));
                    outside_fns.insert(def_id);
                }
                let mode = if cx.constants.mode(def_id).is_some() {
                    Mode::Spec
                } else {
                    item_attrs.mode.unwrap_or(Mode::Exec)
                };
                cx.fns.insert(
                    def_id.to_def_id(),
                    FnInfo {
                        id: FnId(cx.def_hash(def_id.to_def_id())),
                        mode,
                    },
                );
                fns.push(record(FnStatus::Rejected));
            }
            DefKind::Struct | DefKind::Enum if verus => structs.push(def_id),
            DefKind::Union if verus => item_refusals.push(Refusal::new(
                "adt",
                format!(
                    "{} `{}`",
                    kind.descr(def_id.to_def_id()),
                    tcx.def_path_str(def_id.to_def_id())
                ),
                span,
            )),
            DefKind::Impl { of_trait: true } if verus => {
                match (!cx.derived_clones.implementation(def_id))
                    .then(|| trait_impl_problem(tcx, def_id, loose))
                    .flatten()
                    .or_else(|| impl_header_problem(&cx, def_id))
                {
                    Some(refusal) => item_refusals.push(refusal),
                    None => read_items.push(def_id),
                }
            }
            // A trait has checks of its own (bounds, associated types); a
            // trait the reader does not model is refused even without
            // methods.
            DefKind::Trait if verus => match trait_problem(tcx, def_id, loose) {
                Some(refusal) => {
                    if is_plain_trait(tcx, def_id) {
                        pending_item_refusals.push(refusal);
                    } else {
                        item_refusals.push(refusal);
                    }
                }
                None => match where_refusal(&cx, def_id.to_def_id()) {
                    Some(refusal) => item_refusals.push(refusal),
                    None => read_items.push(def_id),
                },
            },
            // An inherent impl is only a container; its methods are read as
            // functions. Its bounds are checked with them.
            DefKind::Impl { of_trait: false } if verus => {
                if let Some(refusal) = where_refusal(&cx, def_id.to_def_id()) {
                    item_refusals.push(refusal);
                }
            }
            DefKind::Trait | DefKind::Impl { of_trait: false } | DefKind::AssocTy => {}
            DefKind::Use | DefKind::ExternCrate | DefKind::Mod | DefKind::Macro(_) => {}
            _ if verus => item_refusals.push(Refusal::new(
                "item-kind",
                format!("{} items are not read yet", kind.descr(def_id.to_def_id())),
                span,
            )),
            _ => {}
        }
        for (name, attr_span) in item_attrs.unsupported {
            if verus {
                item_refusals.push(Refusal::new("attribute", name, attr_span));
            }
        }
    }

    // Local datatypes: registered first so field types can refer to each other,
    // then lowered.
    for def_id in &structs {
        let generics = tcx.generics_of(def_id.to_def_id());
        if generics
            .own_params
            .iter()
            .any(|p| matches!(p.kind, mty::GenericParamDefKind::Const { .. }))
        {
            item_refusals.push(Refusal::new(
                "generics",
                format!(
                    "{} `{}` with const parameters",
                    tcx.def_kind(*def_id).descr(def_id.to_def_id()),
                    tcx.def_path_str(def_id.to_def_id())
                ),
                tcx.def_span(*def_id),
            ));
        } else {
            let id = AdtId(cx.def_hash(def_id.to_def_id()));
            cx.adts.insert(def_id.to_def_id(), id);
        }
    }
    if let Some(imports) = cx.imports.take() {
        match imports.install(&mut cx, &mut krate) {
            Ok(()) => cx.imports = Some(imports),
            Err(reason) => item_refusals.push(Refusal::new(
                "import-binding",
                reason,
                tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
            )),
        }
    }
    // A datatype is refused when one of its fields cannot be represented,
    // which may be because a field datatype was refused; repeat until no
    // more are refused, so that no lowered struct refers to a refused one.
    let mut lowered = Vec::new();
    let (mut wrapper_errors, wrapper_no_base, wrapper_affected) = loop {
        lowered.clear();
        // Facts borrow this exact immutable Cx for the entire lowering pass.
        // Drop them before removing refused types and repeating the pass.
        let wrappers = imports::wrappers::Checks::capture(&cx, &structs, &pending_recursion);
        let mut refused = Vec::new();
        for def_id in &structs {
            let Some(id) = cx.adt_id(def_id.to_def_id()) else {
                continue;
            };
            if let Some(reason) = wrappers.unknown(*def_id) {
                item_refusals.push(Refusal::new(
                    "foreign-field-policy",
                    reason,
                    tcx.def_span(*def_id),
                ));
                refused.push(*def_id);
                continue;
            }
            match datatypes::lower(&cx, *def_id, id, &wrappers) {
                Ok(decl) => lowered.push((*def_id, decl)),
                Err(refusal) => {
                    refused.push(*def_id);
                    item_refusals.push(refusal);
                }
            }
        }
        if refused.is_empty() {
            let affected = structs
                .iter()
                .copied()
                .filter(|owner| wrappers.affected(*owner))
                .collect::<HashSet<_>>();
            let (errors, no_base) = match wrappers.diagnostics() {
                Ok(checked) => checked,
                Err(reason) => {
                    item_refusals.push(Refusal::new(
                        "foreign-field-policy",
                        reason,
                        tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
                    ));
                    (Vec::new(), HashSet::new())
                }
            };
            break (errors, no_base, affected);
        }
        drop(wrappers);
        for def_id in refused {
            cx.adts.remove(&def_id.to_def_id());
        }
    };
    // Every datatype needs a base case ([`recursive_types`]). A refused
    // struct refuses the crate, so the lowered structs are all of Verus's
    // datatypes.
    let mut in_verus_order: Vec<(LocalDefId, &AdtDecl)> = lowered
        .iter()
        .map(|(def_id, decl)| (*def_id, decl))
        .collect();
    let module_index = module_places(tcx);
    in_verus_order.sort_by_key(|(def_id, _)| verus_place(tcx, &module_index, *def_id));
    let original_ground = in_verus_order
        .iter()
        .copied()
        .filter(|(owner, _)| !wrapper_affected.contains(owner))
        .collect::<Vec<_>>();
    let mut unfounded_ids = wrapper_no_base
        .iter()
        .filter_map(|owner| cx.adt_id(owner.to_def_id()))
        .collect::<HashSet<_>>();
    if let Some(owner) = recursive_types::first_unfounded(&cx, &original_ground) {
        if let Some(id) = cx.adt_id(owner.to_def_id()) {
            unfounded_ids.insert(id);
        }
    }
    let unfounded = recursive_types::first_unfounded_in(&cx, &in_verus_order, &unfounded_ids);
    match local_variant_fields::Local::capture(tcx, &lowered) {
        Ok(scope) => cx.local_variant_fields = scope,
        Err(reason) => item_refusals.push(Refusal::new(
            "local-variant-intrinsic",
            reason,
            tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
        )),
    }
    let mut checked_enum_diagnostics = Vec::new();
    for pending in pending_enum_diagnostics {
        match pending.finish(&cx) {
            Ok(checked) => {
                cx.enum_diagnostics.insert(checked.definition());
                checked_enum_diagnostics.push(checked);
            }
            Err(reason) => item_refusals.push(Refusal::new(
                "enum-diagnostic",
                reason,
                tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
            )),
        }
    }
    krate.adts.extend(lowered.into_iter().map(|(_, decl)| decl));

    // Specification methods and the declarations they specify
    // (`vir/src/headers.rs`, `make_trait_decls`).
    for spec in spec_candidates {
        match trait_spec_declaration(tcx, spec) {
            Some(decl) => {
                cx.spec_methods.insert(decl, spec);
            }
            None => errors.push(UserError::new(
                Phase::RustToVir,
                sig_span(tcx, spec),
                messages::traits::NO_MATCHING_METHOD,
            )),
        }
    }

    // Functions.
    let mut verify_refusals = Vec::new();
    // The trait method declarations with a default body, before a mode
    // error takes a body away.
    let mut default_bodies: HashSet<FnId> = HashSet::new();
    let mut ghost_ownership = HashMap::new();
    let mut ghost_work = ownership::ghost_only::Work::new();
    for record in &mut fns {
        if !matches!(record.status, FnStatus::Rejected) {
            continue;
        }
        let owned = |mut error: UserError| {
            error.function = Some(record.def_id);
            error
        };
        if let Some(refusal) = external_trait_bound(tcx, record.def_id, opts.no_external_by_default)
            .or_else(|| dropped_supertrait_bound(tcx, record.def_id, opts.no_external_by_default))
        {
            verify_refusals.push(refusal);
        }
        // Verus checks modes after building VIR: a function with a mode
        // error is still read, for the errors of the phase that builds VIR,
        // and is never verified. The mode checker's error is the function's
        // only error of that phase: it is the first one Verus meets.
        // The mode rules of code outside `verus!` differ (no ghost
        // blocks); the reader does not check them there.
        let mode_check = if outside_fns.contains(&record.def_id) {
            modes::ModeCheck::Unknown(Refusal::new(
                modes::TAG_MODES_UNKNOWN,
                "a function outside verus!",
                tcx.def_span(record.def_id),
            ))
        } else {
            modes::check_fn(&cx, record.def_id)
        };
        let mode_error = match &mode_check {
            modes::ModeCheck::Error(error) => Some(error.clone()),
            _ => None,
        };
        if let modes::ModeCheck::Clean(checked) = &mode_check {
            cx.checked_modes
                .borrow_mut()
                .insert(record.def_id, std::rc::Rc::new(checked.clone()));
        }
        // Constant initialization has no function-shaped ownership body or
        // signature. Its immutable value is checked through Body::Constant;
        // it cannot mint tracked function ownership from a proxy signature.
        if cx.constants.mode(record.def_id).is_none() {
            if let modes::ModeCheck::Clean(checked) = &mode_check {
                if let Some(ghost) =
                    ownership::ghost_only::classify(&cx, record.def_id, checked, &mut ghost_work)
                {
                    ghost_ownership.insert(record.def_id, ghost);
                }
                if let Some(ownership) = ownership::classify(&cx, record.def_id, checked) {
                    cx.native_ownership
                        .borrow_mut()
                        .insert(record.def_id, ownership);
                }
            }
        }
        let mut outcome = body::read_fn(&cx, record.def_id, mode_error.is_some());
        if outside_fns.contains(&record.def_id) {
            outcome.errors.retain(|e| e.phase == Phase::RustToVir);
        }
        if let Some(mode_error) = mode_error {
            errors.extend(
                outcome
                    .errors
                    .into_iter()
                    .filter(|e| e.phase != Phase::Modes)
                    .map(owned),
            );
            errors.push(owned(mode_error));
            record.status = match outcome.result {
                Ok(mut decl) => {
                    if decl.role == trust_vc_vcir::FnRole::TraitDecl
                        && decl.body != trust_vc_vcir::Body::None
                    {
                        default_bodies.insert(decl.id);
                    }
                    // Only the signature stays, for the calls of other
                    // functions: the body and clauses may hold what the
                    // mode checker rejected, and are never verified.
                    decl.body = trust_vc_vcir::Body::None;
                    decl.requires.clear();
                    decl.ensures.clear();
                    decl.recommends.clear();
                    krate.fns.push(decl);
                    FnStatus::Rejected
                }
                Err(body::FnProblem::Refused(refusal)) => FnStatus::Refused(refusal),
                Err(body::FnProblem::Rejected(error)) => {
                    errors.push(owned(error));
                    FnStatus::Rejected
                }
            };
            continue;
        }
        errors.extend(outcome.errors.into_iter().map(owned));
        fn_warnings.extend(outcome.warnings.into_iter().map(owned));
        verify_refusals.extend(outcome.verify_refusal);
        record.status = match outcome.result {
            Ok(decl) => {
                if decl.role == trust_vc_vcir::FnRole::TraitDecl
                    && decl.body != trust_vc_vcir::Body::None
                {
                    default_bodies.insert(decl.id);
                }
                if let modes::ModeCheck::Unknown(refusal) = mode_check {
                    // A mode error Verus reports before verifying may hide
                    // in what the mode checker did not model.
                    verify_refusals.push(refusal);
                }
                let id = decl.id;
                krate.fns.push(decl);
                match outcome.deferred {
                    Some(span) => FnStatus::Deferred(span),
                    None => FnStatus::Read(id),
                }
            }
            Err(body::FnProblem::Refused(refusal)) => FnStatus::Refused(refusal),
            Err(body::FnProblem::Rejected(error)) => {
                errors.push(owned(error));
                FnStatus::Rejected
            }
        };
    }

    // Instances, in the order calls asked for them; reading one may ask for
    // more. What an instance holds is its generic function's, whose errors
    // are reported for the generic function; an instance that cannot be read
    // leaves its callers unverifiable.
    let mut instance_count = 0;
    while let Some((def_id, args, id)) = cx.next_instance() {
        instance_count += 1;
        if instance_count > MAX_INSTANCES {
            verify_refusals.push(Refusal::new(
                "instances",
                format!("more than {MAX_INSTANCES} instances of generic functions"),
                tcx.def_span(def_id),
            ));
            break;
        }
        match body::read_instance(&cx, def_id, args, id) {
            Ok(decl) => krate.fns.push(decl),
            Err(body::FnProblem::Refused(refusal)) => verify_refusals.push(refusal),
            Err(body::FnProblem::Rejected(error)) => verify_refusals.push(Refusal::new(
                "instance",
                format!(
                    "`{}` at {args:?}: {}",
                    tcx.def_path_str(def_id.to_def_id()),
                    error.message
                ),
                error.span,
            )),
        }
    }

    // `vir/src/well_formed.rs`, `check_function`, on Verus's copy of a
    // default method for an implementation that inherits it
    // (`vir/src/traits.rs`, `inherit_default_bodies`): unless the method is
    // public, the copy is visible only in the implementation's module, and
    // its body keeps the default method's visibility (the method's own for
    // an `open` spec method, its module's otherwise), which must be no wider.
    // Verus checks the copies after every other function.
    for imp in &read_items {
        if tcx.def_kind(*imp) != (DefKind::Impl { of_trait: true }) {
            continue;
        }
        let impl_module = tcx.parent_module_from_def_id(*imp).to_def_id();
        for method in cycles::inherited_defaults(tcx, *imp) {
            let Some(info) = cx.fns.get(&method.to_def_id()) else {
                continue;
            };
            let mty::Visibility::Restricted(visible_in) = tcx.visibility(method.to_def_id()) else {
                continue;
            };
            let open = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(method))).open
                || tcx.def_kind(method) == DefKind::AssocConst;
            let body_module = if info.mode == Mode::Spec && open {
                visible_in.to_def_id()
            } else {
                tcx.parent_module_from_def_id(method).to_def_id()
            };
            if !tcx.is_descendant_of(body_module, impl_module) {
                errors.push(UserError::new(
                    Phase::WellFormed,
                    sig_span(tcx, method),
                    messages::traits::INHERITED_BODY_MORE_PUBLIC,
                ));
            }
        }
    }

    // Verus checks the datatypes' base cases last in its well-formedness
    // pass (`vir/src/well_formed.rs`, `check_crate`), and only when no
    // earlier check there failed: the error belongs to no function, so it
    // sorts after every other error of the phase.
    wrapper_errors.sort_by_key(|(owner, _)| verus_place(tcx, &module_index, *owner));
    errors.extend(wrapper_errors.into_iter().map(|(_, error)| error));
    if let Some(def_id) = unfounded {
        errors.push(UserError::new(
            Phase::WellFormed,
            tcx.hir_span_with_body(tcx.local_def_id_to_hir_id(def_id)),
            messages::NO_BASE_VARIANT,
        ));
    }

    let fn_defs: HashMap<FnId, LocalDefId> = cx
        .fns
        .iter()
        .filter_map(|(def_id, info)| def_id.as_local().map(|local| (info.id, local)))
        .collect();
    let order = verus_fn_order(tcx, &fns);
    let cycles = cycles::find(
        &cx,
        &krate,
        &fn_defs,
        &cx.instance_sources(),
        &read_items,
        &order,
    );
    verify_refusals.extend(cycles.refusals);
    errors.extend(cycles.errors);
    krate.def_order = cycles.def_order;
    krate.rec_groups = cycles.groups;
    module_hidden_definitions(tcx, &mut krate, &fn_defs);
    errors.extend(termination::crate_errors(
        &cx,
        &mut krate,
        &fn_defs,
        &default_bodies,
    ));
    // A `when` or `decreases_by` Verus rejects (reported where the function
    // was read) is not kept: the crate is rejected.
    for decl in &mut krate.fns {
        if decl.mode != Mode::Spec {
            decl.decreases_by = None;
            decl.decreases_when = None;
        }
        if decl.decreases.is_empty() {
            decl.decreases_when = None;
        }
    }
    let mut warnings = termination::crate_warnings(&cx, &krate, &fn_defs);
    warnings.append(&mut fn_warnings);
    let fn_modules = fns
        .iter()
        .filter(|f| !matches!(f.status, FnStatus::External))
        .map(|f| tcx.parent_module_from_def_id(f.def_id).to_local_def_id())
        .collect();
    if let Some(scope) = &cx.local_variant_fields {
        if let Err(reason) = scope.revalidate(tcx) {
            item_refusals.push(Refusal::new(
                "local-variant-intrinsic",
                reason,
                tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
            ));
        }
    }
    for checked in &checked_enum_diagnostics {
        if let Err(reason) = checked.revalidate(&cx) {
            item_refusals.push(Refusal::new(
                "enum-diagnostic",
                reason,
                tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
            ));
        }
    }
    if let Err(refusal) = ghost_tail_agreement::check(&cx, &krate) {
        verify_refusals.push(refusal);
    }
    if let Some(nominals) = spec.and_then(|scope| scope.source_nominals) {
        if let Err(reason) = nominals.revalidate(tcx) {
            item_refusals.push(Refusal::new(
                "source-opaque-context",
                reason,
                tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID),
            ));
        }
    }
    let spans = cx.spans.into_inner();
    let explicit_returns = cx.explicit_returns.into_inner();
    let native_ownership = cx.native_ownership.into_inner().into_keys().collect();
    CrateRead {
        read_options: opts,
        krate,
        spec_definitions: cx.spec_definitions,
        spans,
        explicit_returns,
        fns,
        item_refusals,
        pending_item_refusals,
        verify_refusals,
        errors,
        warnings,
        fn_defs,
        order,
        fn_modules,
        native_ownership,
        ghost_ownership,
    }
}

/// The spec definitions a function may not see because Verus shows their
/// bodies only in part of the crate (`rust_to_vir_func.rs`,
/// `get_body_visibility_and_fuel`; `ast_util.rs`, `is_body_visible_to`): an
/// `open` body where the function is visible, any other in its own module
/// and the modules inside it. A function checked outside that part sees the
/// spec function uninterpreted, which [`DefOrder::Later`] states.
fn module_hidden_definitions(
    tcx: TyCtxt<'_>,
    krate: &mut VcCrate,
    fn_defs: &HashMap<FnId, LocalDefId>,
) {
    let region = |def: LocalDefId| -> Option<rustc_hir::def_id::DefId> {
        let open = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(def))).open
            || tcx.def_kind(def) == DefKind::AssocConst;
        let vis = if open {
            tcx.visibility(def.to_def_id())
        } else {
            mty::Visibility::Restricted(tcx.parent_module_from_def_id(def).to_mod_id())
        };
        match vis {
            mty::Visibility::Public => None,
            mty::Visibility::Restricted(module) => Some(module.to_def_id()),
        }
    };
    let hidden_bodies: Vec<(FnId, rustc_hir::def_id::DefId)> = krate
        .fns
        .iter()
        .filter(|d| {
            d.mode == Mode::Spec
                && matches!(
                    d.body,
                    trust_vc_vcir::Body::Spec(_) | trust_vc_vcir::Body::Constant(_)
                )
        })
        .filter_map(|d| {
            let def = *fn_defs.get(&d.id)?;
            Some((d.id, region(def)?))
        })
        .collect();
    if hidden_bodies.is_empty() {
        return;
    }
    let checked: Vec<(FnId, LocalDefId)> = krate
        .fns
        .iter()
        .filter(|d| {
            let recursive_spec = d.mode == Mode::Spec
                && matches!(
                    d.body,
                    trust_vc_vcir::Body::Spec(_) | trust_vc_vcir::Body::Constant(_)
                )
                && krate.rec_group(d.id).is_some();
            (d.mode != Mode::Spec
                && matches!(d.body, trust_vc_vcir::Body::Stmts(_))
                && !d.attrs.external_body
                && d.role != trust_vc_vcir::FnRole::Instance)
                || (matches!(d.body, trust_vc_vcir::Body::Constant(_))
                    && !d.attrs.external_body
                    && d.role != trust_vc_vcir::FnRole::Instance)
                || recursive_spec
        })
        .filter_map(|d| Some((d.id, *fn_defs.get(&d.id)?)))
        .collect();
    for (function, def) in checked {
        let module = tcx.parent_module_from_def_id(def).to_def_id();
        for (spec, visible_in) in &hidden_bodies {
            if !tcx.is_descendant_of(module, *visible_in) {
                krate
                    .def_order
                    .entry(function)
                    .or_default()
                    .insert(*spec, trust_vc_vcir::DefOrder::Later);
            }
        }
    }
}

/// Does `def`'s body open it to a path (`open(in path)`, which `verus!`
/// marks on a `use` item inside the body)?
pub(crate) fn has_open_qualifier(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    tcx.hir_crate_items(()).owners().any(|owner| {
        tcx.def_kind(owner.def_id) == DefKind::Use
            && tcx.opt_local_parent(owner.def_id) == Some(def)
            && attrs::verus_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner.def_id)))
                .iter()
                .any(|(attr, _)| *attr == VerusAttr::OpenVisibilityQualifier)
    })
}

/// Each module's place in crate order: where its `mod` item is; the crate
/// root comes first.
fn module_places(tcx: TyCtxt<'_>) -> HashMap<LocalDefId, usize> {
    let mut module_index: HashMap<LocalDefId, usize> = HashMap::new();
    for (index, owner) in tcx.hir_crate_items(()).owners().enumerate() {
        if matches!(tcx.def_kind(owner.def_id), DefKind::Mod) {
            module_index.entry(owner.def_id).or_insert(index);
        }
    }
    module_index
}

/// Where Verus puts the item `def_id` among the functions or the datatypes
/// of the crate (`vir/src/ast_sort.rs`, `sort_krate`): grouped by module,
/// deeper modules first, then modules in crate order, then source order.
/// Verus reads the methods of a trait or an implementation with it, in
/// source order (`rust_to_vir.rs`, `crate_to_vir`); rustc lists them after
/// the module's other items.
fn verus_place(
    tcx: TyCtxt<'_>,
    module_index: &HashMap<LocalDefId, usize>,
    def_id: LocalDefId,
) -> (std::cmp::Reverse<usize>, usize, rustc_span::BytePos) {
    let module = tcx.parent_module_from_def_id(def_id).to_local_def_id();
    let depth = tcx.def_path(module.to_def_id()).data.len();
    let place = module_index.get(&module).copied().unwrap_or(0);
    (std::cmp::Reverse(depth), place, tcx.def_span(def_id).lo())
}

/// See [`CrateRead::verus_order`]. `fns` is in crate order.
fn verus_fn_order(tcx: TyCtxt<'_>, fns: &[FnRecord]) -> HashMap<LocalDefId, usize> {
    let module_index = module_places(tcx);
    let key = |index: usize| (verus_place(tcx, &module_index, fns[index].def_id), index);
    let mut indices: Vec<usize> = (0..fns.len()).collect();
    indices.sort_by_key(|index| key(*index));
    indices
        .into_iter()
        .enumerate()
        .map(|(position, index)| (fns[index].def_id, position))
        .collect()
}

/// A trait with no type parameters, no supertraits or where clauses, and
/// only associated types without bounds, as written. Building VIR for such a
/// trait cannot fail (`rust_to_vir_trait.rs` has nothing to reject in it), so
/// it does not change which first-phase Verus errors a crate has.
fn is_plain_trait(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let rustc_hir::Node::Item(item) = tcx.hir_node_by_def_id(def_id) else {
        return false;
    };
    let rustc_hir::ItemKind::Trait {
        generics,
        bounds,
        items,
        ..
    } = item.kind
    else {
        return false;
    };
    generics.params.is_empty()
        && generics.predicates.is_empty()
        && bounds.is_empty()
        && items.iter().all(|id| {
            matches!(
                tcx.hir_trait_item(*id).kind,
                rustc_hir::TraitItemKind::Type([], None)
            )
        })
}

/// The span of a function's signature, where Verus reports problems with the
/// function as a whole; the item's span when there is no signature.
pub(crate) fn sig_span(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Span {
    tcx.hir_node_by_def_id(def_id)
        .fn_sig()
        .map_or_else(|| tcx.def_span(def_id), |sig| sig.span)
}

/// Why the reader does not read the trait `def_id`, if it does not. It
/// reads a trait whose only generic parameter is `Self`, whose items are
/// methods, and whose supertraits are `Sized` and traits of this crate that
/// `verus!` produced.
fn trait_problem(tcx: TyCtxt<'_>, def_id: LocalDefId, loose: bool) -> Option<Refusal> {
    let span = tcx.def_span(def_id);
    let refuse = |detail: String| Some(Refusal::new("trait", detail, span));
    let generics = tcx.generics_of(def_id);
    if generics
        .own_params
        .iter()
        .any(|p| matches!(p.kind, mty::GenericParamDefKind::Const { .. }))
    {
        return refuse("a trait with const parameters".to_string());
    }
    if tcx.trait_def(def_id).safety.is_unsafe() {
        return refuse("an unsafe trait".to_string());
    }
    // Bounds on `Self` (supertraits) and on the trait's type parameters:
    // positive bounds by `Sized` and its relatives and by traits the reader
    // reads.
    let bound_ok = |clause: mty::Clause<'_>| match clause.kind().skip_binder() {
        mty::ClauseKind::Trait(t) => {
            matches!(t.self_ty().kind(), mty::Param(_))
                && t.polarity == mty::ClausePolarity::Positive
                && (t.def_id() == def_id.to_def_id()
                    || is_sizedness_trait(tcx, t.def_id())
                    || is_verus_trait(tcx, t.def_id(), loose))
        }
        _ => false,
    };
    for (clause, _) in tcx.explicit_super_clauses_of(def_id).skip_binder() {
        if !bound_ok(*clause) {
            return refuse(format!("a trait bound `{clause}`"));
        }
    }
    let own = tcx.explicit_clauses_of(def_id);
    if let Some((pred, _)) = own.clauses.iter().find(|(pred, _)| !bound_ok(*pred)) {
        return refuse(format!("a where clause `{pred}`"));
    }
    for item in tcx.associated_items(def_id).in_definition_order() {
        match item.kind {
            mty::AssocKind::Fn { .. } => {
                if tcx
                    .generics_of(item.def_id)
                    .own_params
                    .iter()
                    .any(|p| matches!(p.kind, mty::GenericParamDefKind::Const { .. }))
                {
                    return refuse(format!(
                        "the trait method `{}` has const parameters",
                        item.name()
                    ));
                }
            }
            mty::AssocKind::Type { .. } => {
                return refuse(format!("the associated type {}", assoc_type_name(item)))
            }
            mty::AssocKind::Const { .. } => {}
        }
    }
    None
}

/// A bound of the function `def_id`, or of the impl or trait around it,
/// that fixes an associated type of a trait Verus has not been told about:
/// one of another crate (or outside `verus!`), as in `F: Fn()` (whose
/// `FnOnce::Output` is `()`) or `I: Iterator<Item = u8>`. Verus warns about
/// every bound on such a trait (`vir/src/traits.rs`,
/// `demote_external_traits`) and verifies on, but for this kind its SMT
/// encoding refers to a projection it never declares and it fails with an
/// internal error. The reader refuses the function once nothing else
/// rejects the crate.
fn external_trait_bound(tcx: TyCtxt<'_>, def_id: LocalDefId, loose: bool) -> Option<Refusal> {
    let mut predicates = tcx.clauses_of(def_id).clauses.to_vec();
    let parent = tcx.local_parent(def_id);
    if matches!(tcx.def_kind(parent), DefKind::Impl { .. } | DefKind::Trait) {
        predicates.extend_from_slice(tcx.clauses_of(parent).clauses);
    }
    for (clause, span) in predicates {
        let mty::ClauseKind::Projection(p) = clause.kind().skip_binder() else {
            continue;
        };
        let trait_id = p.projection_term.trait_def_id(tcx);
        if !is_verus_trait(tcx, trait_id, loose) {
            return Some(Refusal::new(
                "external-bound",
                format!(
                    "a bound on an associated type of `{}`, a trait Verus has not been told about",
                    tcx.def_path_str(trait_id)
                ),
                span,
            ));
        }
    }
    None
}

/// A bound of the function `def_id`, or of the impl or trait around it, on
/// a trait Verus does not read, from which rustc derives a bound on a trait
/// Verus reads: `X: Sub` with `trait Sub: Q` outside `verus!` gives
/// `X: Q`. Verus drops a bound on a trait it does not read, with a warning
/// (`vir/src/traits.rs`, `demote_external_traits`), and states supertraits
/// only for its own traits (`trait_bound_axioms`), so `X: Q` is not among
/// the function's facts there. The reader decides bounds in rustc's
/// parameter environment of the function, which has it: a definition
/// guarded by `X: Q` (an implementation's spec method, or one under a
/// method's `where Self: Q`) would be visible to the reader and hidden from
/// Verus. A derived bound that the function's bounds on Verus's traits give
/// anyway is not counted. The reader refuses the function, whether or not
/// it uses such a definition, once nothing else rejects the crate.
fn dropped_supertrait_bound(tcx: TyCtxt<'_>, def_id: LocalDefId, loose: bool) -> Option<Refusal> {
    let mut predicates = tcx.clauses_of(def_id).clauses.to_vec();
    let parent = tcx.local_parent(def_id);
    if matches!(tcx.def_kind(parent), DefKind::Impl { .. } | DefKind::Trait) {
        predicates.extend_from_slice(tcx.clauses_of(parent).clauses);
    }
    let read = |trait_id: DefId| is_verus_trait(tcx, trait_id, loose);
    let (kept, dropped): (Vec<_>, Vec<_>) =
        predicates
            .into_iter()
            .partition(|(clause, _)| match clause.kind().skip_binder() {
                mty::ClauseKind::Trait(pred) => {
                    read(pred.def_id()) || is_sizedness_trait(tcx, pred.def_id())
                }
                _ => true,
            });
    // The bounds Verus has: its own traits' bounds and their supertraits,
    // which are again its own traits or sizedness ([`trait_problem`]).
    let kept: HashSet<mty::Clause<'_>> =
        mty::elaborate::elaborate(tcx, kept.into_iter().map(|(clause, _)| clause))
            .map(|clause| tcx.erase_and_anonymize_regions(clause))
            .collect();
    for (clause, span) in dropped {
        for derived in mty::elaborate::elaborate(tcx, [clause]) {
            let mty::ClauseKind::Trait(pred) = derived.kind().skip_binder() else {
                continue;
            };
            if read(pred.def_id()) && !kept.contains(&tcx.erase_and_anonymize_regions(derived)) {
                return Some(Refusal::new(
                    "external-supertrait",
                    format!(
                        "the bound `{clause}` gives `{derived}` through a trait Verus has not been told about"
                    ),
                    span,
                ));
            }
        }
    }
    None
}

/// An associated type's name, as `` `T` ``, or what the compiler made it
/// for: the hidden type of an `async fn` or of a method returning `impl
/// Trait`, which has no name.
fn assoc_type_name(item: &mty::AssocItem) -> String {
    match item.opt_name() {
        Some(name) if !item.is_impl_trait_in_trait() => format!("`{name}`"),
        _ => "of an `async fn` or of a method returning `impl Trait`".to_string(),
    }
}

/// `Sized`, `MetaSized` or `PointeeSized`.
fn is_sizedness_trait(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let items = tcx.lang_items();
    [
        items.sized_trait(),
        items.meta_sized_trait(),
        items.pointee_sized_trait(),
    ]
    .contains(&Some(def_id))
}

/// A trait of this crate that `verus!` produced (or any trait, when
/// `loose`: `--no-external-by-default`), Verus does not ignore, and the
/// reader reads.
pub(crate) fn is_verus_trait(tcx: TyCtxt<'_>, def_id: DefId, loose: bool) -> bool {
    thread_local! {
        /// The traits whose bounds are being examined; a trait met again
        /// while its own bounds are examined is taken as read (the cycle
        /// check refuses the cycle).
        static IN_PROGRESS: RefCell<HashSet<LocalDefId>> = RefCell::new(HashSet::new());
    }
    let Some(local) = def_id.as_local() else {
        return false;
    };
    if tcx.def_kind(local) != DefKind::Trait
        || !(loose
            || attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local))).verus_macro)
        || is_external(tcx, local)
    {
        return false;
    }
    if !IN_PROGRESS.with(|set| set.borrow_mut().insert(local)) {
        return true;
    }
    let ok = trait_problem(tcx, local, loose).is_none();
    IN_PROGRESS.with(|set| set.borrow_mut().remove(&local));
    ok
}

/// Is `def_id` a datatype in the VIR Verus builds (`rust_to_vir.rs`): a
/// struct, enum or union of this crate in `verus!` (or anywhere, under
/// `--no-external-by-default`) and not external. Without vstd, which the
/// reader refuses, no other crate gives Verus a datatype.
pub(crate) fn is_verus_datatype(cx: &Cx<'_>, def_id: DefId) -> bool {
    let tcx = cx.tcx;
    if !def_id.is_local() && cx.imported_nominal(def_id).is_some() {
        return true;
    }
    let Some(local) = def_id.as_local() else {
        return false;
    };
    matches!(
        tcx.def_kind(local),
        DefKind::Struct | DefKind::Enum | DefKind::Union
    ) && (cx.opts.no_external_by_default
        || attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local))).verus_macro)
        && !is_external(tcx, local)
}

/// Is `def_id` a trait implementation of this crate that Verus reads: in
/// `verus!` (or anywhere, under `--no-external-by-default`) and not external?
pub(crate) fn is_verus_trait_impl(cx: &Cx<'_>, def_id: DefId) -> bool {
    let tcx = cx.tcx;
    let Some(local) = def_id.as_local() else {
        return false;
    };
    matches!(tcx.def_kind(local), DefKind::Impl { of_trait: true })
        && (cx.opts.no_external_by_default
            || attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local))).verus_macro)
        && !is_external(tcx, local)
}

/// Why the reader does not read the derived trait implementation `def_id`,
/// if Verus reads it. Verus verifies a derived impl of a type it reads as
/// part of that type (`external.rs`, `get_attrs_for_automatic_derive`),
/// except for the derives it ignores (`automatic_derive.rs`,
/// `get_action`); a derived `Clone` has a body that Verus checks. The
/// reader does not read derived code, so such an impl with items is
/// refused.
fn derived_impl_problem(tcx: TyCtxt<'_>, def_id: LocalDefId, loose: bool) -> Option<Refusal> {
    let trait_id = tcx
        .impl_trait_ref(def_id)
        .instantiate_identity()
        .skip_normalization()
        .def_id;
    let ignored = tcx.get_diagnostic_name(trait_id).is_some_and(|name| {
        matches!(
            name.as_str(),
            "PartialEq" | "Eq" | "Hash" | "Default" | "Debug" | "Ord" | "PartialOrd"
        )
    });
    if ignored || tcx.associated_item_def_ids(def_id).is_empty() {
        return None;
    }
    let mty::Adt(adt, _) = tcx.type_of(def_id).skip_binder().kind() else {
        return None;
    };
    let local = adt.did().as_local()?;
    let read =
        loose || attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(local))).verus_macro;
    if !read || is_external(tcx, local) {
        return None;
    }
    Some(Refusal::new(
        "derive",
        format!(
            "a derived `{}` impl, which Verus verifies",
            tcx.def_path_str(trait_id)
        ),
        tcx.def_span(def_id),
    ))
}

/// Why the reader does not read the trait implementation `def_id`, if it
/// does not. It reads an implementation, without generic parameters, of a
/// trait it reads, whose items are methods.
pub(crate) fn trait_impl_problem(
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    loose: bool,
) -> Option<Refusal> {
    let span = tcx.def_span(def_id);
    let refuse = |tag: &'static str, detail: String| Some(Refusal::new(tag, detail, span));
    let trait_ref = tcx
        .impl_trait_ref(def_id)
        .instantiate_identity()
        .skip_normalization();
    let is_drop = Some(trait_ref.def_id) == tcx.lang_items().drop_trait();
    if !is_drop && !is_verus_trait(tcx, trait_ref.def_id, loose) {
        return refuse(
            "trait-impl",
            format!(
                "an implementation of `{}`, which is not a trait the reader reads",
                tcx.def_path_str(trait_ref.def_id)
            ),
        );
    }
    if tcx.impl_polarity(def_id) != mty::ImplPolarity::Positive {
        return refuse("trait-impl", "a negative trait implementation".to_string());
    }
    if tcx
        .generics_of(def_id)
        .own_params
        .iter()
        .any(|p| matches!(p.kind, mty::GenericParamDefKind::Const { .. }))
    {
        return refuse(
            "generics",
            "a trait implementation with const parameters".to_string(),
        );
    }
    // Positive trait bounds and outlives bounds only.
    if let Some((pred, _)) = tcx
        .explicit_clauses_of(def_id)
        .clauses
        .iter()
        .find(|(pred, _)| match pred.kind().skip_binder() {
            mty::ClauseKind::Trait(t) => t.polarity != mty::ClausePolarity::Positive,
            mty::ClauseKind::RegionOutlives(_) | mty::ClauseKind::TypeOutlives(_) => false,
            _ => true,
        })
    {
        return refuse("generics", format!("a trait implementation bound `{pred}`"));
    }
    for item in tcx.associated_items(def_id).in_definition_order() {
        match item.kind {
            mty::AssocKind::Fn { .. } => {}
            mty::AssocKind::Type { .. } => {
                return refuse(
                    "trait-impl",
                    format!("the associated type {}", assoc_type_name(item)),
                )
            }
            mty::AssocKind::Const { .. } => {}
        }
    }
    None
}

/// A bound of `def_id` with a type Verus does not translate
/// ([`Cx::verus_where_problem`]).
fn where_refusal(cx: &Cx<'_>, def_id: DefId) -> Option<Refusal> {
    match cx.verus_where_problem(def_id) {
        Ok(Some((problem, span))) => Some(Refusal::new(
            TAG_VERUS_TYPE,
            format!("{problem} in a bound, which Verus does not translate"),
            span,
        )),
        Ok(None) => None,
        Err(problem) => Some(problem),
    }
}

/// A bound of the datatype or trait implementation `def_id` on a trait
/// that Verus's trait-conflict check (`trait_conflicts.rs`,
/// `gen_check_trait_impl_conflicts`) names without declaring it. That check
/// rebuilds every datatype and every implementation of a crate trait, with
/// their bounds, as Rust code, and declares only the crate's traits; a bound
/// on any other trait (`Copy`, `Clone`, ...) is an unknown trait there, which
/// rustc reports as Verus's error. Bounds on `Send`, `Sync` and `Unpin` are
/// dropped before (`check_generic_bound`), and sizedness and `Tuple` bounds
/// are written another way.
fn trait_check_bound_refusal(cx: &Cx<'_>, def_id: LocalDefId) -> Option<Refusal> {
    let tcx = cx.tcx;
    let lang = tcx.lang_items();
    let loose = cx.opts.no_external_by_default;
    for (clause, span) in tcx.clauses_of(def_id).clauses {
        let trait_id = match clause.kind().skip_binder() {
            mty::ClauseKind::Trait(pred) => pred.def_id(),
            mty::ClauseKind::Projection(pred) => pred.projection_term.trait_def_id(tcx),
            _ => continue,
        };
        let declared = [
            lang.unpin_trait(),
            lang.sync_trait(),
            tcx.get_diagnostic_item(rustc_span::sym::Send),
            lang.sized_trait(),
            lang.meta_sized_trait(),
            lang.pointee_sized_trait(),
            lang.tuple_trait(),
        ]
        .contains(&Some(trait_id))
            || is_verus_trait(tcx, trait_id, loose);
        if !declared {
            return Some(Refusal::new(
                "trait-check-bound",
                format!(
                    "a bound on `{}`, which Verus's trait-conflict check does not declare",
                    tcx.def_path_str(trait_id)
                ),
                *span,
            ));
        }
    }
    None
}

/// What Verus rejects in the header of the trait implementation `def_id`
/// (`rust_to_vir_impl.rs`, `trait_impl_to_vir`): the implementations that
/// meet the trait's bounds at the implementation's arguments, the self type
/// and trait arguments, and the implementation's own bounds.
fn impl_header_problem(cx: &Cx<'_>, def_id: LocalDefId) -> Option<Refusal> {
    let tcx = cx.tcx;
    let impl_id = def_id.to_def_id();
    let span = tcx.def_span(def_id);
    let trait_ref = tcx
        .impl_trait_ref(def_id)
        .instantiate_identity()
        .skip_normalization();
    let mut header = match cx.verus_bounds_problem(trait_ref.def_id, trait_ref.args, impl_id) {
        Ok(problem) => problem,
        Err(problem) => return Some(problem),
    };
    if header.is_none() {
        for arg in trait_ref.args.iter() {
            match cx.verus_arg_problem(arg, impl_id) {
                Ok(Some(problem)) => {
                    header = Some(problem);
                    break;
                }
                Ok(None) => {}
                Err(problem) => return Some(problem),
            }
        }
    }
    if let Some(problem) = header {
        return Some(Refusal::new(
            TAG_VERUS_TYPE,
            format!("{problem} in a trait implementation's header, which Verus does not translate"),
            span,
        ));
    }
    // Verus's well-formedness check runs over the self type and trait
    // arguments of every trait implementation (`well_formed.rs`,
    // `check_crate`, `trait_impls`).
    for ty in trait_ref.args.types() {
        match cx.verus_wf_problem(ty, impl_id) {
            Ok(Some(problem)) => {
                return Some(Refusal::new(
                    TAG_VERUS_WF,
                    format!("{problem} in a trait implementation's header"),
                    span,
                ))
            }
            Ok(None) => {}
            Err(problem) => return Some(problem),
        }
    }
    where_refusal(cx, impl_id).or_else(|| trait_check_bound_refusal(cx, def_id))
}
