// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! ROUND-9 REVIEW: THE SPEC-COLLECTION POSITIVE TABLE MATCHED A BARE NAME.
//!
//! `syn_type_string_is_spec_collection` read the head segment of a written type
//! AFTER `syn_type_string_head_segment` strips the module path, so a user TYPE
//! ALIAS that merely SHARES the name of a spec collection read
//! `CollectionOrigin::Spec` while `register_type_aliases` resolved it to
//! whatever it actually names. The receiver then classified GHOST and the
//! closure applied to it was skipped.
//!
//! MEASURED at `16240019`, cache off, every one `Verified` on a body that
//! ALWAYS divides by zero, and every one a non-verify at the std spelling the
//! alias names:
//!
//!   `type Seq = Vec<u64>;`            parameter   -> VERIFIED  (`zv1`)
//!   `type Set = BTreeSet<u64>;`       parameter   -> VERIFIED  (`zv2`)
//!   `type Map = BTreeMap<u64, u64>;`  parameter   -> VERIFIED  (`zv3`)
//!   a struct FIELD spelled with such an alias     -> VERIFIED  (`zv4`)
//!
//! This is round 7's own disclosed residual — "`syn_type_string_head_segment`
//! drops the module path" — measured as a LIVE false verify rather than a
//! latent one, and it reaches BOTH the parameter seam and round 7's
//! field-provenance seam, because both read this one table.
//!
//! THE FIX: every genuine spec collection is written WITH its element arguments
//! (`Seq<T>`, `Set<T>`, `Map<K, V>`, `Multiset<T>`); a bare `Seq` is not a spec
//! type at all. Requiring the argument list costs the spec surface nothing and
//! turns these four into `Unknown`, which fails closed. The EXEC table keeps no
//! such requirement on purpose: reading an exec container is what CHECKS a
//! body, so over-matching there cannot buy a skip.
//!
//! STILL OPEN, and narrower than before: a user GENERIC type named
//! `Seq`/`Set`/`Map`/`Multiset` (`mod m { pub struct Map<K, V> { .. } }`) is
//! written with arguments and is not closed by this. Separating it needs the
//! provenance reading to consult the type registry rather than a string.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn verdict(file: &str, func: &str) -> VerifyResult {
    let path = format!("{}/tests/data/{file}", env!("CARGO_MANIFEST_DIR"));
    trust_vc_core::env::with_serialized_env_vars(&[("TRUST_VC_DISABLE_VC_CACHE", "1")], || {
        verify_function_from_file(&path, func)
    })
    .unwrap_or_else(|e| panic!("extract+verify `{func}` in `{file}` failed: {e:?}"))
}

const SHADOW: &str = "spec_collection_name_shadow_repro.rs";
const CONTROL: &str = "spec_collection_name_shadow_control_repro.rs";

#[test]
fn zv1_zv4_a_name_shared_with_a_spec_collection_is_not_provenance() {
    // The no-sink twin carries the obligation, so a `Verified` with the sink
    // would be a check disabled by ADDING A USE.
    let bare = verdict(SHADOW, "zv5_no_sink_twin");
    assert!(
        !matches!(bare, VerifyResult::Verified),
        "the no-sink twin must carry the obligation; got {bare:?}"
    );
    for func in [
        "zv1_alias_named_seq_over_vec_cx",
        "zv2_alias_named_set_over_btreeset_cx",
        "zv3_alias_named_map_over_btreemap_cx",
        "zv4_field_spelled_with_the_alias_cx",
    ] {
        let v = verdict(SHADOW, func);
        assert!(
            !matches!(v, VerifyResult::Verified),
            "ESCAPING-CLOSURE FALSE-VERIFY: `{func}` must not verify; got {v:?}"
        );
    }
    // THE DECISIVE CONTROLS: the identical bodies at the std spellings the
    // aliases name. Non-verifies before and after, so only the NAME ever
    // distinguished them.
    for func in [
        "zv1b_control_plain_vec_cx",
        "zv2b_control_plain_btreeset_cx",
        "zv3b_control_plain_btreemap_cx",
    ] {
        let v = verdict(SHADOW, func);
        assert!(
            !matches!(v, VerifyResult::Verified),
            "CONTROL WENT UNSOUND: `{func}` must not verify; got {v:?}"
        );
    }
}

/// THE LIAR TWIN. The narrowing is satisfiable by refusing the spec surface
/// outright, so the GENUINE spellings must keep verifying their honest bodies —
/// and `zv10`, the same body at the same element width behind an exec `Vec`,
/// must REFUTE, so the four pins below cannot be met by "spec is always
/// skipped".
#[test]
fn zv6_zv10_the_genuine_spec_spellings_are_untouched() {
    for func in [
        "zv6_genuine_spec_seq_ok",
        "zv7_genuine_spec_set_ok",
        "zv8_genuine_spec_map_ok",
        "zv9_genuine_spec_seq_field_ok",
    ] {
        let v = verdict(CONTROL, func);
        assert!(
            matches!(v, VerifyResult::Verified),
            "OVER-REJECTION: the genuine spec spelling `{func}` must verify; got {v:?}"
        );
    }
    let cx = verdict(CONTROL, "zv10_exec_vec_same_body_cx");
    assert!(
        matches!(cx, VerifyResult::Counterexample { .. }),
        "EXPECTED A REFUTATION: `zv10_exec_vec_same_body_cx` is the refuted half \
         of the decisive pair; got {cx:?}"
    );
}
