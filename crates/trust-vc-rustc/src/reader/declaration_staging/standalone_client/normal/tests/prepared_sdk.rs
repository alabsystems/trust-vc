// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! These controls run inside the existing dedicated genuine producer test.

use super::*;
use crate::reader::declaration_staging::standalone_client::prepared_sdk::PreparedSdk;

#[path = "prepared_sdk_rpc.rs"]
mod rpc;

fn invocation(
    owner: &StandaloneImported<'_>,
    sdk: &PreparedSdk<'_>,
    source: &ClientSource,
    output: &Path,
) -> NormalInvocation {
    let original = request(owner, source, output, &[]);
    let mut split = original.original().unwrap().clone();
    split.verus.extend(
        args::split(&[
            "--import".to_owned(),
            format!("vstd={}", sdk.reference_path().display()),
        ])
        .unwrap()
        .verus,
    );
    let old_macro_directory = owner.macro_files().next().unwrap().path.parent().unwrap();
    for arg in &mut split.rustc {
        if *arg == format!("dependency={}", old_macro_directory.display()) {
            *arg = format!("dependency={}", sdk.root().display());
        } else if let Some((name, path)) = arg.split_once('=') {
            if name == "vstd" || name.starts_with("force:verus_") {
                let filename = if name == "vstd" {
                    std::ffi::OsStr::new("libvstd.rlib")
                } else {
                    Path::new(path).file_name().unwrap()
                };
                *arg = format!("{name}={}", sdk.root().join(filename).display());
            }
        }
    }
    NormalInvocation::derive("owned-prepared-sdk-client".into(), split).unwrap()
}

pub(super) fn check(owner: &StandaloneImported<'_>, root: &Path) {
    let frontend = std::path::PathBuf::from(
        std::env::var_os("TRUST_VC_PREPARED_SDK_FRONTEND")
            .expect("actual freshly compiled rust_verify byte input"),
    );
    let frontend = PinnedFile {
        path: frontend.canonicalize().unwrap(),
        sha256: inputs::digest(&frontend).unwrap(),
    };
    assert!(PreparedSdk::prepare_with_frontends(
        owner,
        &root.join("bad-frontend"),
        &[("libvstd.rlib", frontend.clone())]
    )
    .is_err());
    assert!(PreparedSdk::prepare_with_frontends(
        owner,
        &root.join("duplicate-frontend"),
        &[
            ("rust_verify", frontend.clone()),
            ("rust_verify", frontend.clone())
        ]
    )
    .is_err());
    let sdk = PreparedSdk::prepare_with_frontends(
        owner,
        &root.join("prepared-sdk"),
        &[("rust_verify", frontend)],
    )
    .unwrap();
    assert_eq!(std::fs::read_dir(sdk.root()).unwrap().count(), 7);
    let reference: Value =
        serde_json::from_slice(&std::fs::read(sdk.reference_path()).unwrap()).unwrap();
    assert_eq!(reference["schema"], "trust-vc.native-sdk-reference@1");
    assert_eq!(reference["permission_from_reference"], false);
    assert_eq!(reference["serialized_declarations"], false);
    assert_eq!(reference["serialized_bodies"], false);
    assert!(sdk
        .resolve(owner, &sdk.root().join("rust_verify"))
        .unwrap()
        .is_none());
    assert!(PreparedSdk::prepare(owner, sdk.root()).is_err());
    assert!(PreparedSdk::prepare(owner, Path::new("relative-sdk")).is_err());
    assert!(PreparedSdk::prepare(
        owner,
        &owner
            .library()
            .inputs
            .sources
            .root()
            .join("must-not-create-sdk")
    )
    .is_err());
    let source = client_source(root, "prepared-length", "verus! {\nproof fn length_nonnegative<A>(s: vstd::seq::Seq<A>) { assert(s.len() as int >= 0); }\nproof fn false_negative_length<A>(s: vstd::seq::Seq<A>) { assert((s.len() as int) < 0); }\nproof fn false_zero_length<A>(s: vstd::seq::Seq<A>) { assert(s.len() == 0); }\n}");
    let output = root.join("prepared-client.rmeta");
    // The ordinary entry has no live layout operand binding.
    assert!(macro_context::NormalClientPlan::from_invocation(
        owner,
        &source,
        invocation(owner, &sdk, &source, &output)
    )
    .is_err());
    // Same-target links created outside this exact layout cannot join it.
    let unowned = root.join("unowned-sdk");
    std::fs::create_dir(&unowned).unwrap();
    for entry in std::fs::read_dir(sdk.root()).unwrap() {
        let entry = entry.unwrap();
        if entry.file_type().unwrap().is_symlink() {
            std::os::unix::fs::symlink(
                std::fs::read_link(entry.path()).unwrap(),
                unowned.join(entry.file_name()),
            )
            .unwrap();
        } else {
            std::fs::copy(entry.path(), unowned.join(entry.file_name())).unwrap();
        }
    }
    let mut unowned_request = invocation(owner, &sdk, &source, &output)
        .original()
        .unwrap()
        .clone();
    for arg in &mut unowned_request.rustc {
        *arg = arg.replace(sdk.root().to_str().unwrap(), unowned.to_str().unwrap());
    }
    assert!(macro_context::NormalClientPlan::from_prepared_invocation(
        owner,
        &sdk,
        &source,
        NormalInvocation::derive("unowned-sdk".into(), unowned_request).unwrap()
    )
    .is_err());
    let mut duplicate = invocation(owner, &sdk, &source, &output)
        .original()
        .unwrap()
        .clone();
    duplicate.rustc.extend([
        "--extern".into(),
        format!(
            "duplicate_library={}",
            owner.library().prepared.erase.file.path.display()
        ),
    ]);
    assert!(macro_context::NormalClientPlan::from_prepared_invocation(
        owner,
        &sdk,
        &source,
        NormalInvocation::derive("duplicate-sdk-image".into(), duplicate).unwrap()
    )
    .is_err());
    let supplied = invocation(owner, &sdk, &source, &output);
    let original = supplied.original().unwrap().rustc.clone();
    let original_options = supplied.original().unwrap().verus.clone();
    let plan =
        macro_context::NormalClientPlan::from_prepared_invocation(owner, &sdk, &source, supplied)
            .unwrap();
    assert_eq!(plan.invocation().original().unwrap().rustc, original);
    assert_eq!(
        plan.invocation().original().unwrap().verus,
        original_options
    );
    assert!(!verify_plan(owner, &source, "PreparedSdkLength", &plan, output).unwrap());
    let report: Value = serde_json::from_slice(
        &std::fs::read(owner.library().inputs.output.join("PreparedSdkLength.json")).unwrap(),
    )
    .unwrap();
    let verdict = &report["normal_verdict"];
    assert_eq!(verdict["outcome"], "verification-failed");
    assert_eq!(verdict["erase_exit"], 0);
    assert!(verdict["crate_refusals"].as_array().unwrap().is_empty());
    let functions = verdict["functions"].as_array().unwrap();
    assert_eq!(functions.len(), 3);
    for (name, status, proved, failed) in [
        ("length_nonnegative", "verified", 1, 0),
        ("false_negative_length", "failed", 0, 1),
        ("false_zero_length", "failed", 0, 1),
    ] {
        let function = functions
            .iter()
            .find(|row| row["def_path"] == name)
            .unwrap();
        assert_eq!(function["verdict"], status);
        assert_eq!(function["sites_proved"], proved);
        assert_eq!(function["sites_failed"], failed);
        assert!(function["tag"].is_null());
    }
    assert!(report["verify_argv"]
        .as_array()
        .unwrap()
        .iter()
        .any(|arg| arg
            == &json!(format!(
                "vstd={}",
                sdk.root().join("libvstd.rlib").display()
            ))));
    assert_eq!(
        report["sequence_length_observation"]["permission_from_observation"],
        false
    );
    assert_eq!(
        report["prepared_sdk_native_operand_layout"]["directory"],
        json!(sdk.root())
    );
    assert_eq!(
        report["prepared_sdk_native_operand_layout"]["import_authorized"],
        false
    );
    sdk.check_owner(owner).unwrap();
    rpc::check(owner, &sdk, &source, root);

    let copied_reference = root.join("copied-native-reference.vir");
    std::fs::copy(sdk.reference_path(), &copied_reference).unwrap();
    let mut copied = invocation(owner, &sdk, &source, &root.join("copied-ref.rmeta"))
        .original()
        .unwrap()
        .clone();
    copied
        .verus
        .iter_mut()
        .find(|option| option.name == "import")
        .unwrap()
        .value = Some(format!("vstd={}", copied_reference.display()));
    assert!(macro_context::NormalClientPlan::from_prepared_invocation(
        owner,
        &sdk,
        &source,
        NormalInvocation::derive("copied-reference".into(), copied).unwrap()
    )
    .is_err());

    let altered = PreparedSdk::prepare(owner, &root.join("altered-reference-sdk")).unwrap();
    std::fs::write(altered.reference_path(), b"{}").unwrap();
    assert!(altered.check_owner(owner).is_err());

    let swapped = PreparedSdk::prepare(owner, &root.join("swapped-sdk")).unwrap();
    let pending = macro_context::NormalClientPlan::from_prepared_invocation(
        owner,
        &swapped,
        &source,
        invocation(owner, &swapped, &source, &root.join("swapped.rmeta")),
    )
    .unwrap();
    let link = swapped.root().join("libvstd.rlib");
    std::fs::remove_file(&link).unwrap();
    std::os::unix::fs::symlink(&owner.library().prepared.erase.file.path, &link).unwrap();
    assert!(swapped.check_owner(owner).is_err());
    assert!(pending.check_owner(owner, &source).is_err());
    // A same-target replacement also loses the original link identity.
    let replaced = PreparedSdk::prepare(owner, &root.join("replaced-sdk")).unwrap();
    let link = replaced.root().join("libvstd.rlib");
    let target = std::fs::read_link(&link).unwrap();
    std::fs::remove_file(&link).unwrap();
    std::os::unix::fs::symlink(target, &link).unwrap();
    assert!(replaced.check_owner(owner).is_err());
    let moved = PreparedSdk::prepare(owner, &root.join("moved-sdk")).unwrap();
    std::fs::rename(moved.root(), root.join("retired-sdk")).unwrap();
    std::fs::create_dir(moved.root()).unwrap();
    assert!(moved.check_owner(owner).is_err());
}
