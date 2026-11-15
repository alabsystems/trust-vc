#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""Regression guard for the coverage headline.

The defect this pins out: `corpus_coverage.py` printed a "HEADLINE gate-accepted coverage"
number computed ENTIRELY from the manifest and the upstream tree. It never read gate output,
so it could not move when verification regressed — and on 2026-09-16 it did not: the run lane
fell from 19 green corpus paths to 9 and from 123 declared cases to 35, and the headline
stayed at 152/3774 = 4.0%.

Two properties are asserted here, and both must keep holding:
  * asked for a headline with no gate output, the script FAILS (exit 2) and prints no number;
  * a case counts as VERIFIED only when the gate ran it, on a `passed` path, and the ENGINE
    produced upstream's verdict — a failed path or a wrong engine verdict must drop the
    verified count while leaving the declaration-consistent count alone.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("corpus_coverage.py")

UPSTREAM = """
test_verify_one_file! {
    #[test] good_case verus_code! {
        fn f() {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] bad_case verus_code! {
        fn g() { assert(false); } // FAILS
    } => Err(err) => assert_one_fails(err)
}
"""


def manifest(classification: str = "ported") -> dict:
    return {
        "entries": [
            {
                "upstream_path": "source/rust_verify_test/tests/demo.rs",
                "classification": classification,
                "expected_cases": [
                    {
                        "case_id": "good_case",
                        "upstream_case_id": "good_case",
                        "expected_verdict": "verified",
                        "min_obligations": 1,
                    },
                    {
                        "case_id": "bad_case",
                        "upstream_case_id": "bad_case",
                        "expected_verdict": "counterexample",
                        "min_obligations": 1,
                    },
                ],
            }
        ]
    }


def gate(status: str, verdicts: dict[str, str]) -> dict:
    return {
        "generated_unix_seconds": 4102444800,
        "strict": True,
        "repository": {"trust_vc_head": "0" * 40, "dirty": False},
        "trust_vc_corpus": {
            "attempted_paths": 1,
            "passed_paths": 1 if status == "passed" else 0,
            "failed_paths": 0 if status == "passed" else 1,
            "skipped_entries": 0,
            "results": [
                {
                    "upstream_path": "source/rust_verify_test/tests/demo.rs",
                    "trust_vc_path": "evals/verus/ported/demo.rs",
                    "execution_mode": "direct_source",
                    "status": status,
                    "observed_cases": [
                        {"case_id": cid, "trust_vc_path": "evals/verus/ported/demo.rs", "verdict": v}
                        for cid, v in verdicts.items()
                    ],
                }
            ],
        },
    }


class CorpusCoverageHeadline(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        upstream_dir = root / "verus" / "source" / "rust_verify_test" / "tests"
        upstream_dir.mkdir(parents=True)
        (upstream_dir / "demo.rs").write_text(UPSTREAM, encoding="utf-8")
        self.verus = root / "verus"
        self.manifest_path = root / "verus-tests.json"
        self.manifest_path.write_text(json.dumps(manifest()), encoding="utf-8")
        self.addCleanup(self.tmp.cleanup)

    def run_script(self, *extra: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--verus-path",
                str(self.verus),
                "--manifest",
                str(self.manifest_path),
                *extra,
            ],
            capture_output=True,
            text=True,
            check=False,
        )

    def write_gate(self, name: str, payload: dict) -> str:
        path = Path(self.tmp.name) / name
        path.write_text(json.dumps(payload), encoding="utf-8")
        return str(path)

    def test_no_gate_output_is_a_hard_failure_not_a_fallback(self) -> None:
        result = self.run_script()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("REFUSING", result.stderr)
        # the manifest number must not leak out of the refusal path
        self.assertNotIn("Declaration-consistent", result.stdout)
        self.assertEqual(result.stdout.strip(), "")

    def test_declaration_only_prints_no_headline(self) -> None:
        result = self.run_script("--declaration-only")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("NOT MEASURED", result.stdout)
        self.assertIn("Declaration-consistent (manifest bookkeeping, NOT coverage)", result.stdout)

    def test_gate_json_without_corpus_lane_is_a_hard_failure(self) -> None:
        path = self.write_gate("no-corpus.json", {"trust_vc_corpus": None, "repository": {}})
        result = self.run_script("--gate-json", path)
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("WITHOUT the corpus lane", result.stderr)

    def test_missing_gate_json_is_a_hard_failure(self) -> None:
        result = self.run_script("--gate-json", os.path.join(self.tmp.name, "absent.json"))
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("not found", result.stderr)

    def test_green_path_with_engine_verdicts_counts_as_verified(self) -> None:
        path = self.write_gate(
            "green.json", gate("passed", {"good_case": "verified", "bad_case": "counterexample"})
        )
        result = self.run_script("--gate-json", path, "--json")
        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["headline"]["verified"], 2)
        self.assertEqual(payload["headline"]["declaration_consistent_accepted"], 2)

    def test_failed_path_verifies_nothing_while_the_manifest_number_stands(self) -> None:
        path = self.write_gate(
            "red.json", gate("failed", {"good_case": "verified", "bad_case": "counterexample"})
        )
        payload = json.loads(self.run_script("--gate-json", path, "--json").stdout)
        self.assertEqual(payload["headline"]["verified"], 0)
        self.assertEqual(payload["headline"]["declaration_consistent_accepted"], 2)

    def test_wrong_engine_verdict_is_not_verified(self) -> None:
        path = self.write_gate(
            "wrong.json", gate("passed", {"good_case": "verified", "bad_case": "verified"})
        )
        payload = json.loads(self.run_script("--gate-json", path, "--json").stdout)
        self.assertEqual(payload["headline"]["verified"], 1)
        self.assertEqual(payload["headline"]["declaration_consistent_accepted"], 2)

    def test_case_the_gate_never_ran_is_not_verified(self) -> None:
        path = self.write_gate("partial.json", gate("passed", {"good_case": "verified"}))
        payload = json.loads(self.run_script("--gate-json", path, "--json").stdout)
        self.assertEqual(payload["headline"]["verified"], 1)

    def test_unscheduled_path_is_not_verified(self) -> None:
        payload_gate = gate("passed", {"good_case": "verified", "bad_case": "counterexample"})
        payload_gate["trust_vc_corpus"]["results"][0]["upstream_path"] = (
            "source/rust_verify_test/tests/other.rs"
        )
        path = self.write_gate("elsewhere.json", payload_gate)
        payload = json.loads(self.run_script("--gate-json", path, "--json").stdout)
        self.assertEqual(payload["headline"]["verified"], 0)
        self.assertEqual(payload["headline"]["declaration_consistent_accepted"], 2)

    def test_unsupported_gap_entry_never_carries_verified_coverage(self) -> None:
        self.manifest_path.write_text(json.dumps(manifest("unsupported-gap")), encoding="utf-8")
        path = self.write_gate(
            "gap.json", gate("passed", {"good_case": "verified", "bad_case": "counterexample"})
        )
        payload = json.loads(self.run_script("--gate-json", path, "--json").stdout)
        self.assertEqual(payload["headline"]["verified"], 0)
        self.assertEqual(payload["headline"]["scouting"], 2)

    def test_restricted_denominator_is_disclosed_in_the_json_channel(self) -> None:
        """`--only` makes the headline a per-file number; the JSON must SAY so.

        Without this the JSON of a restricted run is `verified_pct: 100.0` with no
        record of the flag, i.e. indistinguishable from a full-corpus result to any
        dashboard or ledger script that consumes it.
        """
        path = self.write_gate(
            "restrict.json", gate("passed", {"good_case": "verified", "bad_case": "counterexample"})
        )
        full = json.loads(self.run_script("--gate-json", path, "--json").stdout)
        self.assertFalse(full["denominator_restricted"])
        self.assertIsNone(full["restricted_by"])

        only = json.loads(
            self.run_script("--gate-json", path, "--json", "--only", "demo.rs").stdout
        )
        self.assertTrue(only["denominator_restricted"])
        self.assertTrue(only["headline"]["denominator_restricted"])
        self.assertEqual(only["restricted_by"]["only"], "demo.rs")

        accepted = json.loads(
            self.run_script("--gate-json", path, "--json", "--accepted-only").stdout
        )
        self.assertTrue(accepted["denominator_restricted"])
        self.assertTrue(accepted["restricted_by"]["accepted_only"])


if __name__ == "__main__":
    unittest.main()
