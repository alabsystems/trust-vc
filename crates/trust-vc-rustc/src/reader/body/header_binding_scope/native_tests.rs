//! Real native contexts for private inherited-header packet denial controls.
//! No SDK, builtin diagnostic item or verifier permission fixture is used.

extern crate rustc_driver;

use super::*;
use crate::reader::{ReadOptions, modes::CheckedModes, read_crate};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};

static RAN: AtomicBool = AtomicBool::new(false);

struct Reset;
impl Drop for Reset {
    fn drop(&mut self) {
        *INSPECT.lock().unwrap() = None;
    }
}

struct Restore<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    key: LocalDefId,
    value: Option<Rc<CheckedModes<'tcx>>>,
}
impl Drop for Restore<'_, '_> {
    fn drop(&mut self) {
        if let Some(value) = self.value.take() {
            self.cx.checked_modes.borrow_mut().insert(self.key, value);
        }
    }
}

fn deny_substitution<'a, 'tcx>(reader: &FnReader<'a, 'tcx>, source: &Source<'a, 'tcx>) {
    let tcx = reader.tcx;
    if tcx
        .item_name(tcx.local_parent(source.declaration).to_def_id())
        .as_str()
        != "HeaderScopeOnly"
    {
        return;
    }
    RAN.store(true, Ordering::Relaxed);
    let pattern = source.body.params[0].pat;
    assert_eq!(source.mode_for(reader, pattern).unwrap(), Mode::Exec);
    let copied_pattern = *pattern;
    assert!(source.mode_for(reader, &copied_pattern).is_err());
    assert!(
        source
            .mode_for(
                reader,
                tcx.hir_body_owned_by(source.destination_body).params[0].pat
            )
            .is_err()
    );

    let mut wrong = source.clone();
    wrong.destination = source.declaration;
    assert!(wrong.current(reader).is_err());
    let mut wrong = source.clone();
    wrong.destination_body = source.source;
    assert!(wrong.current(reader).is_err());
    let mut wrong = source.clone();
    wrong.source = source.destination_body;
    assert!(wrong.current(reader).is_err());
    let mut wrong = source.clone();
    wrong.body = Box::leak(Box::new(*source.body));
    assert!(wrong.current(reader).is_err());
    let mut stale = source.clone();
    stale.source_modes = Rc::new((*source.source_modes).clone());
    assert!(stale.current(reader).is_err());
    let mut stale = source.clone();
    stale.destination_modes = Rc::new((*source.destination_modes).clone());
    assert!(stale.current(reader).is_err());

    for key in [source.declaration, source.destination] {
        let restore = Restore {
            cx: source.cx,
            key,
            value: source.cx.checked_modes.borrow_mut().remove(&key),
        };
        assert!(restore.value.is_some());
        assert!(source.mode_for(reader, pattern).is_err());
        assert!(
            Source::for_inherited(reader, source.declaration, source.source, source.body).is_err()
        );
        assert!(matches!(
            reader.header_binding_scopes.mode_for(reader, pattern),
            Some(Err(_))
        ));
        drop(restore);
        assert_eq!(source.mode_for(reader, pattern).unwrap(), Mode::Exec);
    }

    let original = reader
        .header_binding_scopes
        .0
        .cell
        .borrow()
        .active
        .clone()
        .unwrap();
    {
        let _nested = reader.header_binding_scopes.enter(source.clone()).unwrap();
        assert!(!Rc::ptr_eq(
            &original,
            reader
                .header_binding_scopes
                .0
                .cell
                .borrow()
                .active
                .as_ref()
                .unwrap()
        ));
        assert!(matches!(
            reader.header_binding_scopes.mode_for(reader, pattern),
            Some(Ok(Mode::Exec))
        ));
    }
    assert!(Rc::ptr_eq(
        &original,
        reader
            .header_binding_scopes
            .0
            .cell
            .borrow()
            .active
            .as_ref()
            .unwrap()
    ));
}

struct Capture {
    ran: bool,
}
impl Callbacks for Capture {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        let _read = read_crate(tcx, ReadOptions::default());
        self.ran = true;
        Compilation::Stop
    }
}

struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

#[test]
fn native_inherited_header_modes_require_exact_current_source_and_destination() {
    let _reset = Reset;
    *INSPECT.lock().unwrap() = Some(deny_substitution);
    RAN.store(false, Ordering::Relaxed);
    let directory = Temp(std::env::temp_dir().join(".ubd").join(format!(
        "trust-vc-header-binding-scope-{}-{}", std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos(),
    )));
    std::fs::create_dir_all(&directory.0).unwrap();
    let source = directory.0.join("source.rs");
    std::fs::write(
        &source,
        r#"
#![feature(register_tool)]
#![register_tool(verus)]
#![allow(dead_code)]
#[verus::internal(verus_macro)]
trait HeaderScopeOnly {
    #[verus::internal(verus_macro)]
    fn checked(value: u64) -> u64 { let local = value; local }
}
#[verus::internal(verus_macro)]
struct Carrier;
#[verus::internal(verus_macro)]
impl HeaderScopeOnly for Carrier {
    #[verus::internal(verus_macro)]
    fn checked(value: u64) -> u64 { value }
}
"#,
    )
    .unwrap();
    let arguments = vec![
        "native-header-binding-scope".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=header_binding_scope".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.0.to_str().unwrap().into(),
        source.to_str().unwrap().into(),
    ];
    let mut capture = Capture { ran: false };
    rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut capture))
        .expect("the real native component control must compile");
    assert!(capture.ran);
    assert!(
        RAN.load(Ordering::Relaxed),
        "the actual native inherited-header factory must be observed"
    );
}
