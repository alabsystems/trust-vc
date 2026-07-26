#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Merge parity gate for trust-vc-native vs trust_mc-ingested fixture runs."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from merge_parity_common import (
    PreparedFixture,
    build_report,
    compare_verdicts,
    is_committed_fixture_path,
    load_json,
    make_mismatch_entry,
    normalize_verdict,
    resolve_bundle_path,
    validate_bundle_prechecks,
    validate_corpus_index,
    validate_manifest_schema,
    write_report,
)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run merge parity checks between trust-vc-native and trust_mc-ingested "
            "normalized verdicts."
        )
    )
    parser.add_argument("--fixtures", type=Path, help="Parity fixture manifests directory")
    parser.add_argument("--trust_mc-repo", type=Path, help="Local trust_mc checkout path")
    parser.add_argument("--report", type=Path, help="Machine-readable report JSON path")
    parser.add_argument("--strict", action="store_true", help="Exit non-zero on mismatches")

    # Internal helper mode for deterministic fixture command execution.
    parser.add_argument("--emit-verdict", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--manifest", type=Path, help=argparse.SUPPRESS)
    parser.add_argument(
        "--engine",
        choices=("trust_vc_native", "trust_mc_ingested"),
        help=argparse.SUPPRESS,
    )
    return parser.parse_args(argv)


def default_engine_command(script_path: Path, manifest_path: Path, engine: str) -> list[str]:
    # Legacy replay-only fallback retained for synthetic tests that verify
    # mismatch normalization without building or running the Rust runner.
    return [
        sys.executable,
        str(script_path),
        "--emit-verdict",
        "--manifest",
        str(manifest_path),
        "--engine",
        engine,
    ]


def interpolate_command_args(
    command: list[str],
    fixture: PreparedFixture,
    engine: str,
    repo_root: Path,
    trust_mc_repo: Path,
) -> list[str]:
    bundle_path = resolve_bundle_path(str(fixture.manifest["bundle_path"]), repo_root).resolve()
    replacements = {
        "{bundle_path}": str(bundle_path),
        "{engine}": engine,
        "{fixture_id}": str(fixture.manifest["fixture_id"]),
        "{manifest_path}": str(fixture.manifest_path.resolve()),
        "{obligation_id}": str(fixture.manifest["obligation_id"]),
        "{repo_root}": str(repo_root),
        "{trust_mc_repo}": str(trust_mc_repo),
    }

    rendered: list[str] = []
    for arg in command:
        expanded = arg
        for token, value in replacements.items():
            expanded = expanded.replace(token, value)
        rendered.append(expanded)
    return rendered


def make_error_verdict(
    fixture_id: str,
    obligation_id: str,
    engine: str,
    reason_class: str,
    raw_reason: str,
) -> dict[str, Any]:
    return {
        "fixture_id": fixture_id,
        "engine": engine,
        "status": "error",
        "obligation_id": obligation_id,
        "obligation_name": obligation_id,
        "model_fingerprint": None,
        "reason_class": reason_class,
        "raw_reason": raw_reason,
    }


def run_engine_command(
    engine: str,
    fixture: PreparedFixture,
    script_path: Path,
    repo_root: Path,
    trust_mc_repo: Path,
) -> dict[str, Any]:
    fixture_id = str(fixture.manifest["fixture_id"])
    obligation_id = str(fixture.manifest["obligation_id"])
    command_key = f"{engine}_command"
    command_template = (
        list(fixture.manifest[command_key])
        if command_key in fixture.manifest
        else default_engine_command(script_path, fixture.manifest_path, engine)
    )
    command = interpolate_command_args(
        command_template,
        fixture,
        engine,
        repo_root,
        trust_mc_repo,
    )

    cwd = repo_root if engine == "trust_vc_native" else trust_mc_repo
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError as exc:
        return make_error_verdict(
            fixture_id,
            obligation_id,
            engine,
            "internal_error",
            f"failed to start command '{command}': {exc}",
        )

    if result.returncode != 0:
        stderr = result.stderr.strip() or "<empty stderr>"
        return make_error_verdict(
            fixture_id,
            obligation_id,
            engine,
            "internal_error",
            f"engine command failed (rc={result.returncode}): {stderr}",
        )

    stdout = result.stdout.strip()
    if not stdout:
        return make_error_verdict(
            fixture_id,
            obligation_id,
            engine,
            "parse_error",
            "engine command produced empty stdout",
        )

    try:
        payload = json.loads(stdout)
    except json.JSONDecodeError as exc:
        return make_error_verdict(
            fixture_id,
            obligation_id,
            engine,
            "parse_error",
            f"engine command stdout is not valid JSON: {exc}",
        )

    if not isinstance(payload, dict):
        return make_error_verdict(
            fixture_id,
            obligation_id,
            engine,
            "parse_error",
            "engine command must output a JSON object",
        )

    payload["fixture_id"] = fixture_id
    payload.setdefault("engine", engine)
    return payload


def print_mismatch_summary(mismatches: list[dict[str, Any]]) -> None:
    for entry in mismatches:
        sys.stderr.write(
            "[merge-parity] "
            f"fixture={entry['fixture_id']} "
            f"kind={entry['mismatch_kind']} "
            f"detail={entry.get('detail', '')}\n"
        )


def load_expected_status_by_manifest(index_path: Path) -> dict[str, str]:
    index_data = load_json(index_path)
    assert isinstance(index_data, dict)

    entries = index_data.get("fixtures")
    assert isinstance(entries, list)

    expected_status_by_manifest: dict[str, str] = {}
    for entry in entries:
        assert isinstance(entry, dict)
        manifest_rel = entry["parity_manifest"]
        expected_status = entry["expected_status"]
        assert isinstance(manifest_rel, str)
        assert isinstance(expected_status, str)
        expected_status_by_manifest[manifest_rel] = expected_status

    return expected_status_by_manifest


def validate_gate_args(args: argparse.Namespace) -> tuple[Path, Path, Path] | None:
    if args.fixtures is None or args.trust_mc_repo is None or args.report is None:
        sys.stderr.write(
            "--fixtures, --trust_mc-repo, and --report are required in gate mode\n"
        )
        return None

    fixtures_dir = args.fixtures.resolve()
    trust_mc_repo = args.trust_mc_repo.resolve()
    report_path = args.report.resolve()

    if not fixtures_dir.is_dir():
        sys.stderr.write(f"fixtures directory does not exist: {fixtures_dir}\n")
        return None
    if not trust_mc_repo.is_dir():
        sys.stderr.write(f"trust_mc repo directory does not exist: {trust_mc_repo}\n")
        return None
    return fixtures_dir, trust_mc_repo, report_path


def discover_manifest_paths(fixtures_dir: Path) -> list[Path]:
    return sorted(path for path in fixtures_dir.glob("*.json") if path.is_file())


def precheck_manifest(
    manifest_path: Path,
    repo_root: Path,
) -> tuple[PreparedFixture | None, list[dict[str, Any]]]:
    fallback_fixture_id = manifest_path.stem

    try:
        manifest = load_json(manifest_path)
    except (OSError, json.JSONDecodeError) as exc:
        return None, [
            make_mismatch_entry(
                fallback_fixture_id,
                "schema_violation",
                f"failed to parse manifest JSON: {exc}",
                None,
                None,
            )
        ]

    committed = is_committed_fixture_path(manifest_path, repo_root)
    manifest_errors = validate_manifest_schema(manifest, committed=committed)
    if manifest_errors:
        fixture_id = str(manifest.get("fixture_id", fallback_fixture_id))
        return None, [
            make_mismatch_entry(
                fixture_id,
                "schema_violation",
                err,
                None,
                None,
            )
            for err in manifest_errors
        ]

    assert isinstance(manifest, dict)
    fixture_id = str(manifest["fixture_id"])
    bundle_path = resolve_bundle_path(str(manifest["bundle_path"]), repo_root)
    if not bundle_path.exists():
        return None, [
            make_mismatch_entry(
                fixture_id,
                "schema_violation",
                f"bundle path does not exist: {bundle_path}",
                None,
                None,
            )
        ]

    try:
        bundle = load_json(bundle_path)
    except (OSError, json.JSONDecodeError) as exc:
        return None, [
            make_mismatch_entry(
                fixture_id,
                "schema_violation",
                f"failed to parse bundle JSON: {exc}",
                None,
                None,
            )
        ]

    metadata = manifest["required_metadata"]
    assert isinstance(metadata, dict)
    bundle_errors = validate_bundle_prechecks(bundle, metadata)
    if bundle_errors:
        return None, [
            make_mismatch_entry(fixture_id, "schema_violation", err, None, None)
            for err in bundle_errors
        ]

    assert isinstance(bundle, dict)
    return PreparedFixture(manifest_path, manifest, bundle), []


def precheck_fixtures(
    manifest_paths: list[Path],
    repo_root: Path,
) -> tuple[list[PreparedFixture], list[dict[str, Any]]]:
    fixtures: list[PreparedFixture] = []
    mismatches: list[dict[str, Any]] = []

    for manifest_path in manifest_paths:
        fixture, fixture_mismatches = precheck_manifest(manifest_path, repo_root)
        mismatches.extend(fixture_mismatches)
        if fixture is not None:
            fixtures.append(fixture)

    return fixtures, mismatches


def append_verdict_errors(
    mismatches: list[dict[str, Any]],
    fixture_id: str,
    label: str,
    errors: list[str],
    trust_vc_verdict: dict[str, Any] | None,
    trust_mc_verdict: dict[str, Any] | None,
) -> None:
    for err in errors:
        mismatches.append(
            make_mismatch_entry(
                fixture_id,
                "schema_violation",
                f"{label} verdict invalid: {err}",
                trust_vc_verdict,
                trust_mc_verdict,
            )
        )


def evaluate_fixture(
    fixture: PreparedFixture,
    script_path: Path,
    repo_root: Path,
    trust_mc_repo: Path,
    expected_status: str | None,
) -> list[dict[str, Any]]:
    fixture_id = str(fixture.manifest["fixture_id"])
    trust_vc_raw = run_engine_command("trust_vc_native", fixture, script_path, repo_root, trust_mc_repo)
    trust_mc_raw = run_engine_command("trust_mc_ingested", fixture, script_path, repo_root, trust_mc_repo)

    trust_vc_verdict, trust_vc_errors = normalize_verdict(trust_vc_raw, "trust_vc_native")
    trust_mc_verdict, trust_mc_errors = normalize_verdict(trust_mc_raw, "trust_mc_ingested")

    mismatches: list[dict[str, Any]] = []
    if trust_vc_errors:
        append_verdict_errors(
            mismatches,
            fixture_id,
            "trust-vc",
            trust_vc_errors,
            trust_vc_raw if isinstance(trust_vc_raw, dict) else None,
            trust_mc_raw if isinstance(trust_mc_raw, dict) else None,
        )
        return mismatches

    if trust_mc_errors:
        append_verdict_errors(
            mismatches,
            fixture_id,
            "trust_mc",
            trust_mc_errors,
            trust_vc_verdict,
            trust_mc_raw if isinstance(trust_mc_raw, dict) else None,
        )
        return mismatches

    assert trust_vc_verdict is not None
    assert trust_mc_verdict is not None
    for mismatch_kind, detail in compare_verdicts(
        fixture.manifest,
        trust_vc_verdict,
        trust_mc_verdict,
        expected_status=expected_status,
    ):
        mismatches.append(
            make_mismatch_entry(
                fixture_id,
                mismatch_kind,
                detail,
                trust_vc_verdict,
                trust_mc_verdict,
            )
        )
    return mismatches


def emit_verdict_mode(args: argparse.Namespace) -> int:
    if args.manifest is None or args.engine is None:
        sys.stderr.write("--emit-verdict requires --manifest and --engine\n")
        return 2

    try:
        manifest = load_json(args.manifest.resolve())
    except (OSError, json.JSONDecodeError) as exc:
        sys.stderr.write(f"failed to read manifest {args.manifest}: {exc}\n")
        return 2

    if not isinstance(manifest, dict):
        sys.stderr.write("manifest root must be an object\n")
        return 2

    key = f"{args.engine}_verdict"
    if key not in manifest:
        sys.stderr.write(f"manifest is missing required verdict field '{key}'\n")
        return 2

    verdict = manifest[key]
    if not isinstance(verdict, dict):
        sys.stderr.write(f"{key} must be an object\n")
        return 2

    payload = dict(verdict)
    payload.setdefault("engine", args.engine)
    sys.stdout.write(json.dumps(payload, sort_keys=True) + "\n")
    return 0


def run_gate(args: argparse.Namespace) -> int:
    validated = validate_gate_args(args)
    if validated is None:
        return 2

    fixtures_dir, trust_mc_repo, report_path = validated

    script_path = Path(__file__).resolve()
    repo_root = script_path.parent.parent.resolve()
    corpus_index_path = fixtures_dir.parent / "corpus_index.json"

    # Corpus index validation (fail-closed before engine execution)
    corpus_errors = validate_corpus_index(corpus_index_path, fixtures_dir, repo_root)
    if corpus_errors:
        mismatches = [
            make_mismatch_entry(
                "corpus_index",
                "schema_violation",
                err,
                None,
                None,
            )
            for err in corpus_errors
        ]
        manifest_paths = discover_manifest_paths(fixtures_dir)
        report = build_report(fixtures_dir, len(manifest_paths), mismatches)
        write_report(report_path, report)
        print_mismatch_summary(mismatches)
        return 1

    expected_status_by_manifest = load_expected_status_by_manifest(corpus_index_path)
    manifest_paths = discover_manifest_paths(fixtures_dir)
    if not manifest_paths:
        sys.stderr.write(f"no parity manifest files found in {fixtures_dir}\n")
        return 2

    fixtures, mismatches = precheck_fixtures(manifest_paths, repo_root)
    if not mismatches:
        for fixture in fixtures:
            manifest_rel = f"parity/{fixture.manifest_path.name}"
            expected_status = expected_status_by_manifest.get(manifest_rel)
            if expected_status is None:
                mismatches.append(
                    make_mismatch_entry(
                        str(fixture.manifest["fixture_id"]),
                        "schema_violation",
                        f"corpus index missing expected_status for manifest '{manifest_rel}'",
                        None,
                        None,
                    )
                )
                continue
            mismatches.extend(
                evaluate_fixture(
                    fixture,
                    script_path,
                    repo_root,
                    trust_mc_repo,
                    expected_status,
                )
            )

    report = build_report(fixtures_dir, len(manifest_paths), mismatches)
    write_report(report_path, report)

    if mismatches:
        print_mismatch_summary(mismatches)
        return 1 if args.strict else 0
    return 0


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if args.emit_verdict:
        return emit_verdict_mode(args)
    return run_gate(args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
