# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Shared utilities for merge parity gate validation and reporting."""

from __future__ import annotations

import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ALLOWED_STATUSES = {"verified", "counterexample", "unknown", "error"}
ALLOWED_REASON_CLASSES = {
    "timeout",
    "solver_unknown",
    "unsupported_construct",
    "parse_error",
    "internal_error",
}
ALLOWED_EXPECTED_CLASSES = {"requires", "ensures", "assert", "decreases", "trigger"}
ERROR_KINDS = {"schema_violation", "engine_error"}
EXECUTABLE_BUNDLE_VERSION = 3
EXECUTABLE_EXPRESSION_FORMAT = "smt_lib2_term_v1"
REQUIRED_MANIFEST_FIELDS = (
    "fixture_id",
    "bundle_path",
    "obligation_id",
    "expected_classes",
    "allow_unknown",
    "require_counterexample_model",
    "required_metadata",
)
REQUIRED_CORPUS_ENTRY_FIELDS = (
    "fixture_id",
    "parity_manifest",
    "bundle_path",
    "obligation_id",
    "expected_status",
    "expected_classes",
    "allow_unknown",
    "require_counterexample_model",
    "required_metadata",
)

# Canonical root for committed parity fixtures. Manifests under this path
# must use command-driven execution and must NOT carry inline verdict payloads.
COMMITTED_FIXTURE_ROOT = "crates/trust-vc-merge-contract/fixtures/parity"


@dataclass(frozen=True)
class PreparedFixture:
    manifest_path: Path
    manifest: dict[str, Any]
    bundle: dict[str, Any]


def is_committed_fixture_path(manifest_path: Path, repo_root: Path) -> bool:
    """Return True if the manifest lives under the committed parity fixture root."""
    try:
        rel = manifest_path.resolve().relative_to(repo_root.resolve())
    except ValueError:
        return False
    return str(rel).replace("\\", "/").startswith(COMMITTED_FIXTURE_ROOT + "/")


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def ensure_non_empty_string(value: Any, field: str, errors: list[str]) -> None:
    if not isinstance(value, str) or not value.strip():
        errors.append(f"'{field}' must be a non-empty string")


def ensure_boolean(value: Any, field: str, errors: list[str]) -> None:
    if not isinstance(value, bool):
        errors.append(f"'{field}' must be a boolean")


def validate_manifest_expected_classes(value: Any, errors: list[str]) -> None:
    if not isinstance(value, list) or not value:
        errors.append("'expected_classes' must be a non-empty list")
        return

    invalid = [
        item
        for item in value
        if not isinstance(item, str) or item not in ALLOWED_EXPECTED_CLASSES
    ]
    if invalid:
        errors.append(
            "'expected_classes' contains invalid entries: "
            + ", ".join(str(item) for item in invalid)
        )


def validate_manifest_metadata(value: Any, errors: list[str]) -> None:
    if not isinstance(value, dict):
        errors.append("'required_metadata' must be an object")
        return

    for key in ("source_repo", "source_backend", "capabilities"):
        if key not in value:
            errors.append(f"'required_metadata.{key}' is required")
            continue
        ensure_non_empty_string(value[key], f"required_metadata.{key}", errors)


def validate_engine_config(
    manifest: dict[str, Any],
    engine: str,
    *,
    committed: bool = False,
) -> list[str]:
    errors: list[str] = []
    verdict_key = f"{engine}_verdict"
    command_key = f"{engine}_command"

    has_verdict = verdict_key in manifest
    has_command = command_key in manifest

    if committed:
        if has_verdict:
            errors.append(
                f"committed fixture must not carry '{verdict_key}' "
                f"(replay-only verdicts are only allowed in synthetic tests)"
            )
        if not has_command:
            errors.append(
                f"committed fixture must include '{command_key}' for engine '{engine}'"
            )
    else:
        if not has_verdict and not has_command:
            return [
                f"manifest must include '{verdict_key}' or '{command_key}' for engine '{engine}'"
            ]

    if has_verdict and not isinstance(manifest[verdict_key], dict):
        errors.append(f"'{verdict_key}' must be a JSON object")

    if has_command:
        command = manifest[command_key]
        if not isinstance(command, list) or not command:
            errors.append(f"'{command_key}' must be a non-empty list of command args")
        elif not all(isinstance(arg, str) and arg for arg in command):
            errors.append(f"'{command_key}' entries must be non-empty strings")

    return errors


def validate_manifest_schema(manifest: Any, *, committed: bool = False) -> list[str]:
    if not isinstance(manifest, dict):
        return ["manifest root must be a JSON object"]

    errors: list[str] = []
    for field in REQUIRED_MANIFEST_FIELDS:
        if field not in manifest:
            errors.append(f"missing required field '{field}'")

    if errors:
        return errors

    ensure_non_empty_string(manifest["fixture_id"], "fixture_id", errors)
    ensure_non_empty_string(manifest["bundle_path"], "bundle_path", errors)
    ensure_non_empty_string(manifest["obligation_id"], "obligation_id", errors)
    validate_manifest_expected_classes(manifest["expected_classes"], errors)
    ensure_boolean(manifest["allow_unknown"], "allow_unknown", errors)
    ensure_boolean(
        manifest["require_counterexample_model"], "require_counterexample_model", errors
    )
    validate_manifest_metadata(manifest["required_metadata"], errors)

    for engine in ("trust_vc_native", "trust_mc_ingested"):
        errors.extend(validate_engine_config(manifest, engine, committed=committed))

    return errors


def resolve_bundle_path(bundle_path: str, repo_root: Path) -> Path:
    candidate = Path(bundle_path)
    if candidate.is_absolute():
        return candidate
    return repo_root / candidate


def validate_bundle_prechecks(bundle: Any, required_metadata: dict[str, str]) -> list[str]:
    if not isinstance(bundle, dict):
        return ["bundle must be a JSON object"]

    errors: list[str] = []
    if bundle.get("bundle_version") != EXECUTABLE_BUNDLE_VERSION:
        errors.append(f"bundle_version must be {EXECUTABLE_BUNDLE_VERSION}")

    if bundle.get("expression_format") != EXECUTABLE_EXPRESSION_FORMAT:
        errors.append(
            "expression_format must equal "
            f"'{EXECUTABLE_EXPRESSION_FORMAT}'"
        )

    ensure_non_empty_string(bundle.get("source_id"), "source_id", errors)

    assertions = bundle.get("assertions")
    if not isinstance(assertions, list) or not assertions:
        errors.append("assertions must be a non-empty list")

    for key in ("variables", "assumptions", "decreases", "triggers", "metadata"):
        if key not in bundle:
            errors.append(f"bundle missing required field '{key}'")

    metadata = bundle.get("metadata")
    if not isinstance(metadata, dict):
        errors.append("metadata must be an object")
        return errors

    for key, expected in required_metadata.items():
        actual = metadata.get(key)
        if actual != expected:
            errors.append(f"metadata.{key} must equal '{expected}' (found '{actual}')")

    return errors


def _missing_required_verdict_keys(raw: dict[str, Any]) -> list[str]:
    missing: list[str] = []
    for key in ("fixture_id", "status", "obligation_id"):
        if key not in raw:
            missing.append(f"verdict missing required field '{key}'")
    return missing


def _validate_verdict_status(status: Any, errors: list[str]) -> str | None:
    if not isinstance(status, str) or status not in ALLOWED_STATUSES:
        errors.append(
            "verdict.status must be one of " + ", ".join(sorted(ALLOWED_STATUSES))
        )
        return None
    return status


def _validate_verdict_engine(
    raw_engine: Any,
    expected_engine: str,
    errors: list[str],
) -> str | None:
    if not isinstance(raw_engine, str) or not raw_engine:
        errors.append("verdict.engine must be a non-empty string")
        return None
    if raw_engine != expected_engine:
        errors.append(
            f"verdict.engine expected '{expected_engine}' but found '{raw_engine}'"
        )
        return None
    return raw_engine


def _validate_optional_string_field(
    raw: dict[str, Any],
    field: str,
    errors: list[str],
) -> str | None:
    value = raw.get(field)
    if value is not None and not isinstance(value, str):
        errors.append(f"verdict.{field} must be a string when present")
        return None
    return value


def _validate_reason_class(raw: dict[str, Any], errors: list[str]) -> str | None:
    reason_class = raw.get("reason_class")
    if reason_class is None:
        return None
    if not isinstance(reason_class, str):
        errors.append("verdict.reason_class must be a string when present")
        return None
    if reason_class not in ALLOWED_REASON_CLASSES:
        errors.append(
            "verdict.reason_class must be one of "
            + ", ".join(sorted(ALLOWED_REASON_CLASSES))
        )
        return None
    return reason_class


def normalize_verdict(raw: Any, expected_engine: str) -> tuple[dict[str, Any] | None, list[str]]:
    if not isinstance(raw, dict):
        return None, ["verdict payload must be an object"]

    errors = _missing_required_verdict_keys(raw)
    if errors:
        return None, errors

    ensure_non_empty_string(raw["fixture_id"], "verdict.fixture_id", errors)
    ensure_non_empty_string(raw["obligation_id"], "verdict.obligation_id", errors)

    status = _validate_verdict_status(raw["status"], errors)
    _validate_verdict_engine(raw.get("engine", expected_engine), expected_engine, errors)
    obligation_name = _validate_optional_string_field(raw, "obligation_name", errors)
    model_fingerprint = _validate_optional_string_field(raw, "model_fingerprint", errors)
    raw_reason = _validate_optional_string_field(raw, "raw_reason", errors)
    reason_class = _validate_reason_class(raw, errors)

    if errors:
        return None, errors

    assert status is not None
    return {
        "fixture_id": raw["fixture_id"],
        "engine": expected_engine,
        "status": status,
        "obligation_id": raw["obligation_id"],
        "obligation_name": obligation_name,
        "model_fingerprint": model_fingerprint,
        "reason_class": reason_class,
        "raw_reason": raw_reason,
    }, []


def _identity_mismatches(
    fixture_id: str,
    obligation_id: str,
    trust_vc_verdict: dict[str, Any],
    trust_mc_verdict: dict[str, Any],
) -> list[tuple[str, str]]:
    mismatches: list[tuple[str, str]] = []

    if trust_vc_verdict["fixture_id"] != fixture_id or trust_mc_verdict["fixture_id"] != fixture_id:
        mismatches.append(
            (
                "status_mismatch",
                (
                    "fixture_id mismatch: "
                    f"expected='{fixture_id}' "
                    f"trust_vc='{trust_vc_verdict['fixture_id']}' "
                    f"trust_mc='{trust_mc_verdict['fixture_id']}'"
                ),
            )
        )

    if (
        trust_vc_verdict["obligation_id"] != obligation_id
        or trust_mc_verdict["obligation_id"] != obligation_id
    ):
        mismatches.append(
            (
                "status_mismatch",
                (
                    "obligation_id mismatch: "
                    f"expected='{obligation_id}' "
                    f"trust_vc='{trust_vc_verdict['obligation_id']}' "
                    f"trust_mc='{trust_mc_verdict['obligation_id']}'"
                ),
            )
        )

    return mismatches


def _status_mismatches(
    allow_unknown: bool,
    trust_vc_status: str,
    trust_mc_status: str,
) -> tuple[list[tuple[str, str]], bool]:
    mismatches: list[tuple[str, str]] = []

    if trust_vc_status == "error" or trust_mc_status == "error":
        mismatches.append(
            (
                "engine_error",
                f"engine returned error status (trust_vc={trust_vc_status}, trust_mc={trust_mc_status})",
            )
        )
        return mismatches, True

    if (trust_vc_status == "unknown" or trust_mc_status == "unknown") and not allow_unknown:
        mismatches.append(
            (
                "unknown_not_allowed",
                "unknown status is disallowed by fixture (allow_unknown=false)",
            )
        )
        return mismatches, True

    if trust_vc_status != trust_mc_status:
        mismatches.append(
            (
                "status_mismatch",
                f"status mismatch: trust_vc={trust_vc_status}, trust_mc={trust_mc_status}",
            )
        )
        return mismatches, True

    return mismatches, False


def _counterexample_mismatches(
    require_model: bool,
    trust_vc_verdict: dict[str, Any],
    trust_mc_verdict: dict[str, Any],
) -> list[tuple[str, str]]:
    if trust_vc_verdict["status"] != "counterexample" or not require_model:
        return []

    trust_vc_model = trust_vc_verdict.get("model_fingerprint")
    trust_mc_model = trust_mc_verdict.get("model_fingerprint")
    has_trust_vc_model = isinstance(trust_vc_model, str) and bool(trust_vc_model.strip())
    has_trust_mc_model = isinstance(trust_mc_model, str) and bool(trust_mc_model.strip())

    if not has_trust_vc_model or not has_trust_mc_model:
        return [
            (
                "model_mismatch",
                "counterexample model missing with require_counterexample_model=true",
            )
        ]

    if trust_vc_model == trust_mc_model:
        return []

    return [
        (
            "model_mismatch",
            "counterexample model mismatch with require_counterexample_model=true",
        )
    ]


def _unknown_reason_mismatches(
    trust_vc_verdict: dict[str, Any],
    trust_mc_verdict: dict[str, Any],
) -> list[tuple[str, str]]:
    if trust_vc_verdict["status"] != "unknown":
        return []

    trust_vc_reason = trust_vc_verdict.get("reason_class")
    trust_mc_reason = trust_mc_verdict.get("reason_class")
    if trust_vc_reason == trust_mc_reason:
        return []

    return [
        (
            "status_mismatch",
            f"unknown reason_class mismatch: trust_vc={trust_vc_reason}, trust_mc={trust_mc_reason}",
        )
    ]


def _expected_status_mismatches(
    expected_status: str | None,
    trust_vc_verdict: dict[str, Any],
    trust_mc_verdict: dict[str, Any],
) -> list[tuple[str, str]]:
    if expected_status is None:
        return []

    trust_vc_status = trust_vc_verdict["status"]
    trust_mc_status = trust_mc_verdict["status"]
    if trust_vc_status != trust_mc_status or trust_vc_status == expected_status:
        return []

    return [
        (
            "status_mismatch",
            (
                f"expected_status mismatch: expected={expected_status}, "
                f"trust_vc={trust_vc_status}, trust_mc={trust_mc_status}"
            ),
        )
    ]


def compare_verdicts(
    manifest: dict[str, Any],
    trust_vc_verdict: dict[str, Any],
    trust_mc_verdict: dict[str, Any],
    *,
    expected_status: str | None = None,
) -> list[tuple[str, str]]:
    fixture_id = str(manifest["fixture_id"])
    obligation_id = str(manifest["obligation_id"])

    mismatches = _identity_mismatches(
        fixture_id, obligation_id, trust_vc_verdict, trust_mc_verdict
    )

    status_mismatches, terminal = _status_mismatches(
        bool(manifest["allow_unknown"]),
        trust_vc_verdict["status"],
        trust_mc_verdict["status"],
    )
    mismatches.extend(status_mismatches)
    if terminal:
        return mismatches

    expected_status_mismatches = _expected_status_mismatches(
        expected_status,
        trust_vc_verdict,
        trust_mc_verdict,
    )
    mismatches.extend(expected_status_mismatches)
    if expected_status_mismatches:
        return mismatches

    mismatches.extend(
        _counterexample_mismatches(
            bool(manifest["require_counterexample_model"]),
            trust_vc_verdict,
            trust_mc_verdict,
        )
    )
    mismatches.extend(_unknown_reason_mismatches(trust_vc_verdict, trust_mc_verdict))
    return mismatches


def make_mismatch_entry(
    fixture_id: str,
    mismatch_kind: str,
    detail: str,
    trust_vc_verdict: dict[str, Any] | None,
    trust_mc_verdict: dict[str, Any] | None,
) -> dict[str, Any]:
    return {
        "fixture_id": fixture_id,
        "mismatch_kind": mismatch_kind,
        "detail": detail,
        "trust_vc_verdict": trust_vc_verdict,
        "trust_mc_verdict": trust_mc_verdict,
    }


def build_report(
    fixtures_dir: Path,
    total_fixtures: int,
    mismatches: list[dict[str, Any]],
) -> dict[str, Any]:
    mismatched_fixtures = {entry["fixture_id"] for entry in mismatches}
    error_fixtures = {
        entry["fixture_id"]
        for entry in mismatches
        if entry["mismatch_kind"] in ERROR_KINDS
    }

    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "fixtures_dir": str(fixtures_dir),
        "summary": {
            "total_fixtures": total_fixtures,
            "matched": total_fixtures - len(mismatched_fixtures),
            "mismatched": len(mismatched_fixtures),
            "errors": len(error_fixtures),
        },
        "mismatches": mismatches,
    }


def write_report(path: Path, report: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(report, handle, indent=2, sort_keys=True)
        handle.write("\n")


def validate_corpus_index(
    index_path: Path,
    fixtures_dir: Path,
    repo_root: Path,
) -> list[str]:
    """Validate corpus_index.json against on-disk parity manifests and bundles.

    Returns a list of error strings. Empty list means valid.
    """
    errors: list[str] = []

    try:
        index_data = load_json(index_path)
    except (OSError, json.JSONDecodeError) as exc:
        return [f"failed to parse corpus index: {exc}"]

    if not isinstance(index_data, dict):
        return ["corpus index root must be a JSON object"]

    entries = index_data.get("fixtures")
    if not isinstance(entries, list):
        return ["corpus index must contain a 'fixtures' array"]

    # 1. Check required fields and collect fixture_ids
    seen_ids: dict[str, int] = {}
    indexed_manifests: set[str] = set()

    for i, entry in enumerate(entries):
        if not isinstance(entry, dict):
            errors.append(f"corpus index entry {i} must be a JSON object")
            continue

        for field in REQUIRED_CORPUS_ENTRY_FIELDS:
            if field not in entry:
                errors.append(f"corpus index entry {i} missing required field '{field}'")

        fixture_id = entry.get("fixture_id")
        if isinstance(fixture_id, str) and fixture_id:
            if fixture_id in seen_ids:
                errors.append(
                    f"duplicate fixture_id '{fixture_id}' at entries {seen_ids[fixture_id]} and {i}"
                )
            else:
                seen_ids[fixture_id] = i

        parity_manifest = entry.get("parity_manifest")
        if isinstance(parity_manifest, str) and parity_manifest:
            indexed_manifests.add(parity_manifest)

    if errors:
        return errors

    # 2. Verify every referenced parity manifest exists
    for entry in entries:
        manifest_rel = entry["parity_manifest"]
        manifest_path = fixtures_dir.parent / manifest_rel
        if not manifest_path.exists():
            errors.append(
                f"corpus index references missing manifest: {manifest_rel}"
            )

    # 3. Reject extra parity/*.json files not listed in index
    on_disk = {
        f"parity/{p.name}"
        for p in fixtures_dir.glob("*.json")
        if p.is_file()
    }
    extra = on_disk - indexed_manifests
    for extra_manifest in sorted(extra):
        errors.append(
            f"parity manifest on disk but not in corpus index: {extra_manifest}"
        )

    if errors:
        return errors

    # 4. Cross-validate each entry against its manifest and bundle
    for entry in entries:
        fixture_id = entry["fixture_id"]
        manifest_rel = entry["parity_manifest"]
        manifest_path = fixtures_dir.parent / manifest_rel

        try:
            manifest = load_json(manifest_path)
        except (OSError, json.JSONDecodeError) as exc:
            errors.append(f"[{fixture_id}] failed to parse manifest: {exc}")
            continue

        if not isinstance(manifest, dict):
            errors.append(f"[{fixture_id}] manifest root must be a JSON object")
            continue

        # Verify contract fields match
        for field in ("bundle_path", "obligation_id", "expected_classes",
                       "allow_unknown", "require_counterexample_model", "required_metadata"):
            index_val = entry.get(field)
            manifest_val = manifest.get(field)
            if index_val != manifest_val:
                errors.append(
                    f"[{fixture_id}] '{field}' mismatch: "
                    f"index={json.dumps(index_val)}, manifest={json.dumps(manifest_val)}"
                )

        # Verify expected_status matches committed verdicts when a manifest
        # deliberately embeds a synthetic replay verdict. Command-driven
        # manifests have no committed status payload to cross-check here.
        expected_status = entry["expected_status"]
        for engine in ("trust_vc_native", "trust_mc_ingested"):
            verdict_key = f"{engine}_verdict"
            verdict = manifest.get(verdict_key)
            if verdict is None:
                continue
            if isinstance(verdict, dict):
                actual_status = verdict.get("status")
                if actual_status != expected_status:
                    errors.append(
                        f"[{fixture_id}] expected_status '{expected_status}' "
                        f"does not match {verdict_key}.status '{actual_status}'"
                    )

        # Verify required_metadata matches bundle metadata
        bundle_path_str = entry["bundle_path"]
        bundle_path = resolve_bundle_path(bundle_path_str, repo_root)
        if bundle_path.exists():
            try:
                bundle = load_json(bundle_path)
            except (OSError, json.JSONDecodeError):
                continue
            if isinstance(bundle, dict):
                bundle_metadata = bundle.get("metadata", {})
                for key, expected_val in entry["required_metadata"].items():
                    actual_val = bundle_metadata.get(key)
                    if actual_val != expected_val:
                        errors.append(
                            f"[{fixture_id}] required_metadata.{key} mismatch: "
                            f"index='{expected_val}', bundle='{actual_val}'"
                        )

    return errors
