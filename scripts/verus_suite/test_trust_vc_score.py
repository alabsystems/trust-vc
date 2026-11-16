#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Offline tests for the trust-vc front end of run_suite.py and its scoring.

What is pinned here, and why:
  * scoring (trust_vc_score.py): a harness pass counts only with a verdict record
    and no refusal; a refusal counts as refused even when the harness passed; a
    function called verified that holds a line where the reference run reports an
    error is a false pass whatever else happened, and only in the same file; a
    verified function without a reference to check it against is unchecked; a
    record line that is not JSON, or a refused or skipped function with no
    refusal diagnostic in its run, is a bad record, never a pass;
  * examples.rs tests map to the test dir and entry file the harness uses, and two
    examples that share a file stem are told apart by entry file;
  * the --capture-diagnostics wrapper passes rust_verify's stdout, stderr, exit
    status and ending signal through unchanged, and files the stderr under the
    test dir of rustc's -o;
  * staging never deletes through the symlink into the Verus checkout, a trust-vc
    stage holds rust_verify and the three builtin crates and nothing else, and
    re-staging keeps unchanged files (macOS rescans every new executable);
  * the ledger gets one header and one line per run, and the runner refuses a
    trust-vc run without its binary and builtins, or with a solver.
"""
from __future__ import annotations

import argparse
import copy
import csv
import io
import json
import signal
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import run_suite  # noqa: E402
import trust_vc_score as tvs  # noqa: E402

TEST_RS = "/s/stage/source/target.noindex/debug/test_inputs/basic-t/test.rs"
REF_RS = "/r/stage/source/target.noindex/debug/test_inputs/basic-t/test.rs"


def fn(verdict, lines=(1, 5), file=TEST_RS, name="f", tag=None):
    return {"def_path": name, "verdict": verdict, "lines": list(lines), "file": file, "tag": tag,
            "sites_proved": 2 if verdict == "verified" else None, "sites_failed": None}


def record(*functions, refusals=(), entry=TEST_RS):
    return {"schema": "trust-vc.verdict@1", "compiler_commit": "abc", "entry_file": entry,
            "functions": list(functions), "crate_refusals": list(refusals),
            "refused": bool(refusals) or any(f["verdict"] in ("refused", "skipped") for f in functions)}


def error(line, file=REF_RS, primary=True, message="assertion failed"):
    return json.dumps({"level": "error", "message": message, "spans": [
        {"file_name": file, "line_start": line, "is_primary": primary}]})


class ScoreTestTest(unittest.TestCase):
    def score(self, harness, records, reference=((("test.rs", 10),), 0), texts=()):
        ref = None if reference is None else (set(reference[0]), reference[1])
        return tvs.score_test(harness, records, list(texts), ref)

    def test_pass_needs_a_record(self):
        self.assertEqual(self.score("ok", [record(fn("verified"))])["score"], "pass")
        self.assertEqual(self.score("ok", [])["score"], "false-pass")

    def test_vacuous_only_when_the_reference_ran_nothing_either(self):
        s = tvs.score_test("ok", [], [], None, reference_ran=False)
        self.assertEqual((s["score"], s["unchecked_verified_fns"]), ("vacuous", 0))
        self.assertEqual(tvs.score_test("ok", [], [], None, reference_ran=True)["score"], "false-pass")
        self.assertEqual(tvs.score_test("ok", [], [], None, reference_ran=None)["score"], "false-pass")
        # a record means rust_verify ran: scored as usual
        self.assertEqual(tvs.score_test("ok", [record(fn("verified"))], [], None, reference_ran=False)["score"],
                         "pass")

    def test_a_refusal_is_never_a_pass(self):
        s = self.score("ok", [record(fn("verified"), fn("refused", name="g", tag="trait"),
                                     refusals=["trust-vc refused: trait: traits are not read yet"])])
        self.assertEqual((s["score"], s["tags"]), ("refused", "trait"))
        s = self.score("ok", [record(refusals=["trust-vc refused: vstd: programs that use vstd"])])
        self.assertEqual((s["score"], s["tags"]), ("refused", "vstd"))
        s = self.score("ok", [record(fn("skipped", tag=None), refusals=["trust-vc refused: x: y"])])
        self.assertEqual((s["score"], s["tags"]), ("refused", "untagged x"))

    def test_a_refused_or_skipped_function_needs_a_refusal_diagnostic(self):
        for v in ("skipped", "refused"):
            s = self.score("ok", [record(fn(v, tag="no-verify"))])
            self.assertEqual(s["score"], "bad-record", v)
            s = self.score("ok", [record(fn(v, tag="no-verify"),
                                         refusals=["trust-vc refused: no-verify: `f` is not verified"])])
            self.assertEqual(s["score"], "refused", v)

    def test_a_failed_harness_needs_a_tag(self):
        self.assertEqual(self.score("FAILED", [record(fn("failed"))])["score"], "untagged-fail")
        s = self.score("FAILED", [], texts=["error: trust-vc refused: internal-error: boom"])
        self.assertEqual((s["score"], s["tags"]), ("refused", "internal-error"))
        self.assertEqual(self.score("crashed", [])["score"], "untagged-fail")

    def test_verified_over_a_reference_error_is_a_false_pass(self):
        s = self.score("ok", [record(fn("verified", lines=(1, 12)))])
        self.assertEqual(s["score"], "false-pass-ref")
        self.assertEqual(s["false_pass_ref_fns"], "f")
        # it wins over a refusal and over a failed harness
        s = self.score("FAILED", [record(fn("verified", lines=(1, 12)), fn("refused", name="g", tag="x"))])
        self.assertEqual(s["score"], "false-pass-ref")
        # an error in another file of the same test is not this function's
        s = self.score("ok", [record(fn("verified", lines=(1, 12)))], reference=((("m.rs", 10),), 0))
        self.assertEqual(s["score"], "pass")
        # failed, rejected, trusted functions make no claim
        for v in ("failed", "rejected", "trusted", "external"):
            self.assertEqual(self.score("ok", [record(fn(v, lines=(1, 12)))])["score"], "pass", v)

    def test_unchecked_verified(self):
        self.assertEqual(self.score("ok", [record(fn("verified"))], reference=None)["unchecked_verified_fns"], 1)
        s = self.score("ok", [record(fn("verified"))], reference=((), 1))
        self.assertEqual((s["score"], s["unchecked_verified_fns"]), ("pass", 1))
        self.assertEqual(self.score("ignored", [], reference=None)["unchecked_verified_fns"], 0)

    def test_corrupt_record(self):
        self.assertEqual(self.score("ok", [record(fn("verified")), {"corrupt": "{\"sch"}])["score"], "bad-record")


class ReferenceTest(unittest.TestCase):
    def test_errors_are_placed_by_primary_span(self):
        text = "\n".join([
            error(24),
            error(30, primary=False),
            json.dumps({"level": "error", "message": "aborting due to 1 previous error", "spans": []}),
            json.dumps({"level": "warning", "message": "w", "spans": [
                {"file_name": REF_RS, "line_start": 3, "is_primary": True}]}),
            json.dumps({"level": "error", "message": "no span", "spans": []}),
            "exit=1",
        ])
        sites, unplaced = tvs.reference_errors([(None, text)])
        self.assertEqual(sites, {("test.rs", 24)})
        self.assertEqual(unplaced, 2)  # the error whose spans are all secondary, and the spanless one

    def test_norm_file(self):
        self.assertEqual(tvs.norm_file(TEST_RS), "test.rs")
        self.assertEqual(tvs.norm_file("/a/test_inputs/x-y/sub/m.rs"), "sub/m.rs")
        self.assertEqual(tvs.norm_file("../../examples/guide/a.rs"), "examples/guide/a.rs")
        self.assertEqual(tvs.norm_file("/v/examples/guide/a.rs"), "examples/guide/a.rs")


class RejectionParityScoreRunTest(unittest.TestCase):
    """Exercise the real file-based scorer with measured rejection shapes.

    These are ordinary temporary JSON fixtures, not compiler/SDK receipts. The
    native compiler rejected the whole crate before proof; the reference also
    emitted a placed source error, although its diagnostic assertion failed.
    """

    def rejection(self, *functions):
        value = record(*functions)
        value.update(compiler_commit="82bb867eddb94599f68194f701c766f2b6f5a02f",
                     outcome="verus-rejected", exit_code=1, erase_exit=None)
        for function in value["functions"]:
            function["kind"] = "AssocFn"
        return value

    def trait_record(self):
        return self.rejection(fn("external", (24, 24), name="Tr::foo"),
                              fn("external", (24, 24), name="Tr::VERUS_SPEC__foo"))

    def impl_record(self):
        return self.rejection(fn("rejected", (23, 23), name="Tr::foo"),
                              fn("external", (30, 30), name="<X as Tr>::foo"))

    def score_cases(self, cases):
        with tempfile.TemporaryDirectory(prefix="tvs-rejection-parity-") as tmp:
            root = Path(tmp)
            verdicts, logs, reference = root / "verdicts", root / "logs", root / "reference"
            verdicts.mkdir()
            logs.mkdir()
            verus_src = fake_verus(root / "verus") if any(
                case.get("binary") == "examples" for case in cases) else root / "source"
            examples = tvs.example_tests(verus_src)
            rows, outcomes = [], {}
            for index, case in enumerate(cases):
                binary, test = case.get("binary", "diagnostics"), case.get("test_name", f"case_{index}")
                test_dir, _ = tvs.test_dir_of(binary, test, examples)
                native_path = str(root / "stage/source/target.noindex/debug/test_inputs" / test_dir / "test.rs")
                reference_path = REF_RS.replace("basic-t", test_dir)
                rows.append({"binary": binary, "test_name": test,
                             "outcome": case.get("harness", "ok")})
                if "raw_verdict" in case:
                    (verdicts / f"{test_dir}.jsonl").write_text(case["raw_verdict"])
                elif "records" in case:
                    values = copy.deepcopy(case["records"])
                    for value in values:
                        if value.get("entry_file") == TEST_RS:
                            value["entry_file"] = native_path
                        for function in value.get("functions", []):
                            if function.get("file") == TEST_RS:
                                function["file"] = native_path
                    if "modify_records" in case:
                        case["modify_records"](values)
                    (verdicts / f"{test_dir}.jsonl").write_text(
                        "".join(json.dumps(value) + "\n" for value in values))
                captures = case.get("captures", [{"text": case.get("capture", error(24)),
                    "entry": case.get("reference_entry", REF_RS),
                    "exit": case.get("reference_exit", "1")}])
                for capture_index, capture in enumerate(captures):
                    if capture["text"] is None:
                        continue
                    directory = reference / "diags" / test_dir
                    directory.mkdir(parents=True, exist_ok=True)
                    lines = []
                    for line in capture["text"].splitlines():
                        try:
                            diagnostic = json.loads(line)
                        except json.JSONDecodeError:
                            lines.append(line)
                            continue
                        if isinstance(diagnostic, dict):
                            for span in diagnostic.get("spans", []):
                                if span.get("file_name") == REF_RS:
                                    span["file_name"] = reference_path
                                    if "reference_path_alias" in case:
                                        span["file_name"] = case["reference_path_alias"](reference_path)
                        lines.append(json.dumps(diagnostic))
                    header = capture.get("entry", REF_RS)
                    if header == REF_RS:
                        header = reference_path
                        if "reference_path_alias" in case:
                            header = case["reference_path_alias"](reference_path)
                    text = "" if header is None else f"entry={header}\n"
                    text += "\n".join(lines) + "\n"
                    footer = capture.get("exit", "1")
                    if footer is not None:
                        text += f"exit={footer}\n"
                    (directory / f"1-{capture_index}.stderr").write_text(text)
                outcome = case.get("reference_outcome", "FAILED")
                if outcome is not None:
                    outcomes[(binary, test)] = outcome
                if "failed_output" in case:
                    with (logs / f"{binary}.a1.jsonl").open("a") as stream:
                        stream.write(json.dumps({"type": "test", "event": "failed", "name": test,
                                                 "stdout": case["failed_output"]}) + "\n")
            reference_dir = None if all(case.get("no_reference") for case in cases) else reference
            return tvs.score_run(rows, verdicts, logs, verus_src, reference_dir, outcomes)

    def assert_no_match(self, case, score="pass", unchecked=1):
        scored, totals = self.score_cases([case])
        row = scored[0]
        self.assertEqual(row["score"], score)
        self.assertEqual(row["reference_rejection_match"], 0)
        self.assertIs(type(row["reference_rejection_match"]), int)
        self.assertEqual(row["unchecked_verified_fns"], unchecked)
        self.assertEqual(totals["reference_rejection_matches"], 0)
        return row, totals

    def test_actual_trait_and_impl_shapes_do_not_invent_unchecked_functions(self):
        scored, totals = self.score_cases([
            {"records": [self.trait_record()], "capture": error(
                24, message="An individual item of a trait cannot be marked external.")},
            {"records": [self.impl_record()], "capture": error(
                30, message="An individual item of a trait impl cannot be marked external.")},
        ])
        self.assertEqual([row["score"] for row in scored], ["pass", "pass"])
        self.assertEqual([row["reference"] for row in scored], ["FAILED", "FAILED"])
        self.assertEqual([row["verified_fns"] for row in scored], [0, 0])
        self.assertEqual([row["unchecked_verified_fns"] for row in scored], [0, 0])
        self.assertEqual([row["reference_rejection_match"] for row in scored], [1, 1])
        self.assertTrue(all(type(row["reference_rejection_match"]) is int for row in scored))
        self.assertEqual(totals["reference_rejection_matches"], 2)
        self.assertEqual(totals["verified_fns"], 0)
        self.assertEqual(totals["unchecked_verified_fns"], 0)
        self.assertTrue(totals["ok"])

    def test_every_native_record_needs_its_own_placed_error_match(self):
        records = [self.trait_record(), self.impl_record()]
        self.assert_no_match({"records": records, "capture": error(24)})
        scored, totals = self.score_cases([
            {"records": records, "capture": error(24) + "\n" + error(30)}])
        self.assertEqual(scored[0]["records"], 2)
        self.assertEqual(scored[0]["reference_rejection_match"], 1)
        self.assertEqual(scored[0]["unchecked_verified_fns"], 0)
        self.assertEqual(totals["reference_rejection_matches"], 1)  # cases, not records

    def test_acceptance_and_mixed_runs_keep_the_unexpected_pass_guard(self):
        for outcome, exit_code in [("checked", 0), ("verification-failed", 1), ("unknown", 1)]:
            with self.subTest(outcome=outcome):
                accepted = self.trait_record()
                accepted.update(outcome=outcome, exit_code=exit_code)
                self.assert_no_match({"records": [accepted]})
                self.assert_no_match({"records": [self.trait_record(), accepted]})

    def test_normal_exit_and_complete_record_shape_are_required(self):
        mutations = [("exit_code", value) for value in (0, 101, -9, None, True, "1", 1.0)]
        mutations += [("schema", "unknown"), ("outcome", None), ("erase_exit", 0),
                      ("refused", None), ("functions", [])]
        for key, value in mutations:
            with self.subTest(field=key, value=value):
                changed = self.trait_record()
                changed[key] = value
                self.assert_no_match({"records": [changed]})
        for key in ("schema", "outcome", "exit_code", "erase_exit", "refused", "crate_refusals", "functions"):
            with self.subTest(missing=key):
                changed = self.trait_record()
                del changed[key]
                self.assert_no_match({"records": [changed]})

    def test_missing_empty_and_corrupt_verdicts_preserve_existing_scores(self):
        self.assert_no_match({}, score="false-pass", unchecked=0)
        self.assert_no_match({"records": []}, score="false-pass", unchecked=0)
        self.assert_no_match({"raw_verdict": "\n"}, score="false-pass", unchecked=0)
        self.assert_no_match({"raw_verdict": "{not JSON}\n"}, score="bad-record", unchecked=0)

    def test_native_identity_metadata_cannot_be_missing_or_malformed(self):
        for field in ("entry_file", "compiler_commit"):
            for value in (None, "", True, False):
                with self.subTest(field=field, value=value):
                    changed = self.trait_record()
                    changed[field] = value
                    self.assert_no_match({"records": [changed]})
            with self.subTest(missing=field):
                changed = self.trait_record()
                del changed[field]
                self.assert_no_match({"records": [changed]})
        for field, values in [("kind", (None, "", True, "Struct", "unknown")),
                              ("def_path", (None, "", " ", "\t", True, False)),
                              ("tag", ("", True, False, "unsupported"))]:
            for value in values:
                with self.subTest(function_field=field, value=value):
                    changed = self.trait_record()
                    changed["functions"][0][field] = value
                    self.assert_no_match({"records": [changed]})
            with self.subTest(missing_function_field=field):
                changed = self.trait_record()
                del changed["functions"][0][field]
                self.assert_no_match({"records": [changed]})

    def test_function_states_and_site_claims_cannot_be_waived(self):
        for verdict in ("trusted", "failed", "spec", "declared", "unknown", None):
            with self.subTest(verdict=verdict):
                changed = self.trait_record()
                changed["functions"][0]["verdict"] = verdict
                self.assert_no_match({"records": [changed]})
        for field in ("sites_proved", "sites_failed"):
            for value in (1, False, True):
                with self.subTest(field=field, value=value):
                    changed = self.trait_record()
                    changed["functions"][0][field] = value
                    self.assert_no_match({"records": [changed]})
            with self.subTest(missing=field):
                changed = self.trait_record()
                del changed["functions"][0][field]
                self.assert_no_match({"records": [changed]})
        changed = self.trait_record()
        for function in changed["functions"]:
            function.update(sites_proved=0, sites_failed=0)
        scored, _ = self.score_cases([{"records": [changed]}])
        self.assertEqual(scored[0]["reference_rejection_match"], 1)

    def test_reference_conflict_unchecked_and_refusal_precedence_are_unchanged(self):
        verified = self.rejection(fn("verified", (24, 24)))
        row, totals = self.assert_no_match({"records": [verified]}, score="false-pass-ref", unchecked=0)
        self.assertEqual(row["false_pass_ref_fns"], "f")
        self.assertEqual(totals["false_pass_ref"], 1)
        verified = self.rejection(fn("verified", (1, 5)))
        self.assert_no_match({"records": [verified]})
        self.assert_no_match({"records": [verified], "capture": None})
        for verdict in ("refused", "skipped"):
            with self.subTest(verdict=verdict):
                refused = self.rejection(fn(verdict, (24, 24), tag="no-verify"))
                self.assert_no_match({"records": [refused]}, score="bad-record", unchecked=0)
                refused["crate_refusals"] = ["trust-vc refused: no-verify: no proof claim"]
                row, _ = self.assert_no_match({"records": [refused]}, score="refused", unchecked=0)
                self.assertIn("no-verify", row["tags"])
        refusal = self.trait_record()
        refusal.update(refused=True, crate_refusals=["trust-vc refused: trait: unsupported"])
        self.assert_no_match({"records": [refusal]}, score="refused", unchecked=0)
        self.assert_no_match({"records": [verified], "harness": "FAILED",
                              "failed_output": "trust-vc refused: trait: unsupported"},
                             score="refused", unchecked=0)

    def test_native_ranges_and_source_files_are_validated(self):
        for bounds in (None, [], [25, 24], [0, 24], [-1, 24], [True, 24], [24, 24.5]):
            with self.subTest(bounds=bounds):
                changed = self.trait_record()
                changed["functions"][0]["lines"] = bounds
                self.assert_no_match({"records": [changed]})
        for field in ("lines", "file"):
            with self.subTest(missing=field):
                changed = self.trait_record()
                del changed["functions"][0][field]
                self.assert_no_match({"records": [changed]})
        changed = self.trait_record()
        changed["functions"][0]["file"] = ""
        self.assert_no_match({"records": [changed]})

    def test_native_files_cannot_borrow_another_case_or_stage_anchor(self):
        other_case = TEST_RS.replace("basic-t", "diagnostics-other_case")
        same_case_other_stage = "/other/stage/source/target.noindex/debug/test_inputs/diagnostics-case_0/test.rs"
        for path in (other_case, same_case_other_stage):
            with self.subTest(path=path):
                moved = self.trait_record()
                moved["entry_file"] = path
                for function in moved["functions"]:
                    function["file"] = path
                self.assert_no_match({"records": [moved]})
                moved = self.trait_record()
                moved["functions"][0]["file"] = path
                self.assert_no_match({"records": [moved]})

    def test_native_anchor_is_lexical_and_fixture_binding_does_not_repair_aliases(self):
        aliases = {
            "leading whitespace": lambda path: " " + path,
            "trailing whitespace": lambda path: path + " ",
            "relative": lambda path: path.lstrip("/"),
            "parent segment": lambda path: path.replace("/stage/", "/stage/../stage/", 1),
            "dot segment": lambda path: path.replace("/stage/", "/stage/./", 1),
            "repeated slash": lambda path: path.replace("/stage/", "/stage//", 1),
        }
        for name, alias in aliases.items():
            with self.subTest(alias=name):
                def move(values):
                    for value in values:
                        value["entry_file"] = alias(value["entry_file"])
                        for function in value["functions"]:
                            function["file"] = value["entry_file"]
                self.assert_no_match({"records": [self.trait_record()], "modify_records": move})
        for value in (" " + TEST_RS, TEST_RS + " ", TEST_RS.replace("basic-t", "other-case")):
            with self.subTest(unbound_malformed_entry=value):
                changed = self.trait_record()
                changed["entry_file"] = value
                self.assert_no_match({"records": [changed]})

    def test_compiler_commit_requires_the_normal_full_lowercase_identity(self):
        valid = self.trait_record()["compiler_commit"]
        for compiler in ("unknown", "abc", valid[:-1], valid + "0", valid.upper(), "g" * 40,
                         " " + valid, valid + " "):
            with self.subTest(compiler_commit=compiler):
                changed = self.trait_record()
                changed["compiler_commit"] = compiler
                self.assert_no_match({"records": [changed]})

    def test_reference_capture_headers_primary_files_and_exits_must_agree(self):
        wrong_case = REF_RS.replace("basic-t", "diagnostics-other_case")
        same_case_other_stage = "/other/stage/source/target.noindex/debug/test_inputs/diagnostics-case_0/test.rs"
        for header in (None, "", wrong_case, " " + REF_RS, REF_RS + " ",
                       REF_RS.lstrip("/"), REF_RS.replace("/stage/", "/stage/../stage/", 1)):
            with self.subTest(header=header):
                self.assert_no_match({"records": [self.trait_record()], "reference_entry": header})
        for filename in (wrong_case, same_case_other_stage, " " + REF_RS, REF_RS + " "):
            with self.subTest(primary_file=filename):
                self.assert_no_match({"records": [self.trait_record()],
                                      "capture": error(24, file=filename)})
        for exit_code in (None, 0, 101, -9, True, "01", " 1", "1 "):
            with self.subTest(reference_exit=exit_code):
                self.assert_no_match({"records": [self.trait_record()], "reference_exit": exit_code})
        both_files = json.loads(error(24))
        both_files["spans"].append({"file_name": wrong_case, "line_start": 24, "is_primary": True})
        self.assert_no_match({"records": [self.trait_record()], "capture": json.dumps(both_files)})
        for bad_capture in ({"text": error(24), "entry": wrong_case},
                            {"text": error(24), "entry": None},
                            {"text": error(24), "exit": 0}):
            with self.subTest(extra_capture=bad_capture):
                self.assert_no_match({"records": [self.trait_record()],
                                      "captures": [{"text": error(24)}, bad_capture]})

    def test_example_entries_do_not_gain_the_normal_test_rejection_exception(self):
        entry = "../../examples/same.rs"
        changed = self.trait_record()
        changed["entry_file"] = entry
        for function in changed["functions"]:
            function["file"] = entry
        row, _ = self.assert_no_match({"binary": "examples", "test_name": "examples_same",
                                      "records": [changed], "reference_entry": entry,
                                      "capture": error(24, file=entry)})
        self.assertEqual(row["records"], 1)
        self.assertEqual(row["test_dir"], "example-same")

    def test_reference_entry_aliases_remain_invalid_even_when_primary_files_agree(self):
        aliases = {
            "leading whitespace": lambda path: " " + path,
            "trailing whitespace": lambda path: path + " ",
            "relative": lambda path: path.lstrip("/"),
            "parent segment": lambda path: path.replace("/stage/", "/stage/../stage/", 1),
            "dot segment": lambda path: path.replace("/stage/", "/stage/./", 1),
            "repeated slash": lambda path: path.replace("/stage/", "/stage//", 1),
        }
        for name, alias in aliases.items():
            with self.subTest(alias=name):
                self.assert_no_match({"records": [self.trait_record()], "reference_path_alias": alias})

    def test_reference_errors_must_be_captured_placed_and_correlated(self):
        for capture in (None, "", "not JSON", error(24, primary=False),
                        error(24, primary=1), error(24, primary="true"),
                        error(24, file="/reference/unrelated.rs"), error(99),
                        error(24) + "\n" + error(30, primary=False),
                        json.dumps({"level": "error", "message": "no primary span", "spans": []}),
                        json.dumps({"level": "warning", "message": "only warning", "spans": []}),
                        json.dumps({"level": "error", "message": "aborting due to 1 previous error",
                                    "spans": []})):
            with self.subTest(capture=capture):
                self.assert_no_match({"records": [self.trait_record()], "capture": capture})
        self.assert_no_match({"records": [self.trait_record()], "no_reference": True})
        for outcome in ("ignored", "not-run", "crashed", "", None):
            with self.subTest(reference_outcome=outcome):
                self.assert_no_match({"records": [self.trait_record()], "reference_outcome": outcome})
        self.assert_no_match({"records": [self.trait_record()], "reference_outcome": "ok"}, unchecked=0)

    def test_csv_and_summary_expose_the_match_without_changing_reference_outcome(self):
        accepted = self.trait_record()
        accepted.update(outcome="checked", exit_code=0)
        scored, totals = self.score_cases([
            {"records": [self.trait_record()]},
            {"records": [self.impl_record()], "capture": error(30)},
            {"records": [accepted]},
        ])
        self.assertIn("reference_rejection_match", tvs.SCORE_FIELDS)
        output = io.StringIO()
        writer = csv.DictWriter(output, fieldnames=tvs.SCORE_FIELDS)
        writer.writeheader()
        writer.writerows(scored)
        rendered = list(csv.DictReader(io.StringIO(output.getvalue())))
        self.assertEqual([row["reference"] for row in rendered], ["FAILED"] * 3)
        self.assertEqual([row["reference_rejection_match"] for row in rendered], ["1", "1", "0"])
        self.assertEqual([row["unchecked_verified_fns"] for row in rendered], ["0", "0", "1"])
        self.assertEqual(totals["reference_rejection_matches"], 2)
        summary = "\n".join(tvs.summary_lines(scored, totals))
        self.assertIn("| reference_rejection_matches | 2 |", summary)
        self.assertIn("Tests that break the run (1)", summary)


def fake_verus(root: Path) -> Path:
    src = root / "source"
    (src / "rust_verify").mkdir(parents=True)
    (src / "rust_verify_test/tests").mkdir(parents=True)
    (src / "rust_verify_test/tests/examples.rs").write_text(
        'examples_in_dir!("../../examples");\nexamples_in_dir!("../../examples/guide");\n'
        '#[cfg(feature = "singular")]\nexamples_in_dir!("../../examples/missing");\n')
    (root / "examples/guide").mkdir(parents=True)
    for f in ("examples/foo-bar.rs", "examples/a.b.rs", "examples/same.rs", "examples/guide/same.rs",
              "examples/README.md"):
        (root / f).write_text("")
    return src


class ExamplesTest(unittest.TestCase):
    def test_example_test_names_follow_the_macro(self):
        with tempfile.TemporaryDirectory(prefix="tvs-ex-") as tmp:
            ex = tvs.example_tests(fake_verus(Path(tmp)))
            self.assertEqual(ex["examples_foo_bar"], ("example-foo-bar", "../../examples/foo-bar.rs"))
            self.assertEqual(ex["examples_a"], ("example-a.b", "../../examples/a.b.rs"))
            self.assertEqual(ex["examples_same"], ("example-same", "../../examples/same.rs"))
            self.assertEqual(ex["examples_guide_same"], ("example-same", "../../examples/guide/same.rs"))
            self.assertEqual(len(ex), 4)
            self.assertEqual(tvs.test_dir_of("basic", "t", ex), ("basic-t", None))

    def test_score_run_separates_examples_that_share_a_test_dir(self):
        with tempfile.TemporaryDirectory(prefix="tvs-run-") as tmp:
            tmp = Path(tmp)
            verus_src = fake_verus(tmp / "verus")
            vd, logs, ref = tmp / "verdicts", tmp / "logs", tmp / "ref"
            vd.mkdir()
            logs.mkdir()
            top, guide = "../../examples/same.rs", "../../examples/guide/same.rs"
            (vd / "example-same.jsonl").write_text(
                json.dumps(record(fn("verified", lines=(1, 9), file=top), entry=top)) + "\n"
                + json.dumps(record(fn("verified", lines=(1, 9), file=guide), entry=guide)) + "\n")
            (vd / "basic-t.jsonl").write_text(json.dumps(record(fn("verified"))) + "\n")
            (vd / "basic-u.jsonl").write_text(json.dumps(record(fn("failed"))) + "\n")
            cap = ref / "diags/example-same"
            cap.mkdir(parents=True)
            (cap / "1-1.stderr").write_text(f"entry={top}\nexit=0\n")
            (cap / "1-2.stderr").write_text(f"entry={guide}\n{error(4, file='/v/examples/guide/same.rs')}\nexit=1\n")
            (ref / "diags/basic-t").mkdir(parents=True)
            (ref / "diags/basic-t/1-3.stderr").write_text(f"entry={REF_RS}\nexit=0\n")
            (logs / "basic.a1.jsonl").write_text(json.dumps(
                {"type": "test", "event": "failed", "name": "u", "stdout": "trust-vc refused: nope"}) + "\n")
            rows = [{"binary": "examples", "test_name": "examples_same", "outcome": "ok"},
                    {"binary": "examples", "test_name": "examples_guide_same", "outcome": "ok"},
                    {"binary": "basic", "test_name": "t", "outcome": "ok"},
                    {"binary": "basic", "test_name": "u", "outcome": "FAILED"},
                    {"binary": "basic", "test_name": "v", "outcome": "ignored"},
                    {"binary": "examples", "test_name": "examples_foo_bar", "outcome": "ok"},
                    {"binary": "basic", "test_name": "w", "outcome": "ok"}]
            outcomes = {("examples", "examples_same"): "ok", ("examples", "examples_guide_same"): "ok",
                        ("basic", "t"): "ok", ("basic", "u"): "ok", ("basic", "v"): "ignored",
                        ("examples", "examples_foo_bar"): "ok", ("basic", "w"): "FAILED"}
            scored, totals = tvs.score_run(rows, vd, logs, verus_src, ref, outcomes)
            by = {s["test_name"]: s for s in scored}
            self.assertEqual(by["examples_same"]["score"], "pass")
            self.assertEqual(by["examples_same"]["records"], 1)
            self.assertEqual(by["examples_guide_same"]["score"], "false-pass-ref")
            self.assertEqual(by["t"]["score"], "pass")
            self.assertEqual((by["u"]["score"], by["u"]["tags"]), ("refused", "nope"))
            self.assertEqual(by["v"]["score"], "ignored")
            # no record and no capture: the reference ran nothing either
            self.assertEqual(by["examples_foo_bar"]["score"], "vacuous")
            # no capture, but the reference did not pass the test: unknown, so a false pass
            self.assertEqual(by["w"]["score"], "false-pass")
            self.assertEqual((totals["pass"], totals["false_pass_ref"], totals["vacuous"], totals["live"]),
                             (2, 1, 1, 6))
            self.assertFalse(totals["ok"])
            self.assertEqual(totals["compiler_commits"], ["abc"])


class TeeWrapperTest(unittest.TestCase):
    """The wrapper runs under /bin/bash and its "real" rust_verify is /bin/bash
    running a script given as the first argument: macOS holds the first launch
    of every new executable file for a scan, so the test launches none."""

    def run_wrapper(self, tmp: Path, body: str, args):
        real = tmp / "real.sh"
        real.write_text(body)
        w = tmp / "rust_verify"
        w.write_text(run_suite.TEE_WRAPPER.replace("@DYLD@", "/nowhere").replace("@REAL@", "/bin/bash")
                     .replace("@DIAGS@", str(tmp / "diags")))
        return subprocess.run(["/bin/bash", str(w), str(real), *args], capture_output=True, text=True)

    def test_passes_everything_through_and_captures_stderr(self):
        with tempfile.TemporaryDirectory(prefix="tvs-tee-") as tmp:
            tmp = Path(tmp)
            r = self.run_wrapper(tmp, 'echo out; echo \'{"level":"error"}\' >&2; exit 3\n',
                                 ["--cfg", "x.rs", "-o", "/t/test_inputs/basic-t/libtest_crate.rmeta",
                                  "/t/test_inputs/basic-t/test.rs"])
            self.assertEqual((r.returncode, r.stdout, r.stderr), (3, "out\n", '{"level":"error"}\n'))
            caps = list((tmp / "diags/basic-t").glob("*.stderr"))
            self.assertEqual(len(caps), 1)
            self.assertEqual(caps[0].read_text(),
                             'entry=/t/test_inputs/basic-t/test.rs\n{"level":"error"}\nexit=3\n')

    def test_no_capture_without_an_output(self):
        with tempfile.TemporaryDirectory(prefix="tvs-tee-") as tmp:
            r = self.run_wrapper(Path(tmp), "exit 0\n", ["a.rs"])
            self.assertEqual(r.returncode, 0)
            self.assertFalse((Path(tmp) / "diags").exists())

    def test_a_signal_stays_a_signal(self):
        with tempfile.TemporaryDirectory(prefix="tvs-tee-") as tmp:
            r = self.run_wrapper(Path(tmp), "kill -ABRT $$\n", ["-o", "/t/x/l.rmeta", "a.rs"])
            self.assertEqual(r.returncode, -signal.SIGABRT)
            self.assertIn(f"exit={128 + signal.SIGABRT}", next((Path(tmp) / "diags/x").glob("*")).read_text())


def stage_args(frontend="verus", capture=False, rust_verify=None, builtins=None, native_cli_inputs=None):
    return argparse.Namespace(frontend=frontend, capture_diagnostics=capture, rust_verify=rust_verify,
                              builtins=builtins, dyld=Path("/nowhere"),
                              native_cli_inputs=native_cli_inputs or {})


class StageTest(unittest.TestCase):
    def test_staging_modes(self):
        with tempfile.TemporaryDirectory(prefix="tvs-stage-") as tmp:
            tmp = Path(tmp)
            verus_src = tmp / "verus/source"
            real_tv = verus_src / "target-verus/debug"
            real_tv.mkdir(parents=True)
            for f in ("rust_verify", "z3", "libvstd.rlib"):
                (real_tv / f).write_text(f)
            builtins = tmp / "builtins"
            builtins.mkdir()
            for f in run_suite.BUILTIN_ARTIFACTS + ["libsyn.rlib"]:
                (builtins / f).write_text(f)
            ours = tmp / "our_rust_verify"
            ours.write_text("ours")
            label = tmp / "label"
            tv = label / "stage/source/target-verus/debug"
            tv.parent.mkdir(parents=True)

            run_suite.stage_target_verus(tv, verus_src, stage_args(), label)
            self.assertTrue(tv.is_symlink())
            run_suite.stage_target_verus(tv, verus_src, stage_args(capture=True), label)
            self.assertFalse(tv.is_symlink())
            self.assertTrue((tv / "z3").is_symlink())
            self.assertIn(str(real_tv / "rust_verify"), (tv / "rust_verify").read_text())
            run_suite.stage_target_verus(tv, verus_src, stage_args(), label)
            self.assertTrue(tv.is_symlink())
            self.assertEqual(sorted(p.name for p in real_tv.iterdir()), ["libvstd.rlib", "rust_verify", "z3"])

            args = stage_args("trust-vc", rust_verify=ours, builtins=builtins)
            staged = run_suite.stage_target_verus(tv, verus_src, args, label)
            self.assertFalse(tv.is_symlink())
            self.assertEqual(sorted(p.name for p in tv.iterdir()),
                             sorted(run_suite.BUILTIN_ARTIFACTS + ["rust_verify"]))
            self.assertEqual((tv / "rust_verify").read_text(), "ours")
            self.assertEqual(set(staged), set(run_suite.BUILTIN_ARTIFACTS + ["rust_verify"]))
            self.assertEqual(sorted(p.name for p in real_tv.iterdir()), ["libvstd.rlib", "rust_verify", "z3"])
            inode = (tv / "rust_verify").stat().st_ino
            run_suite.stage_target_verus(tv, verus_src, args, label)
            self.assertEqual((tv / "rust_verify").stat().st_ino, inode)

            args = stage_args("trust-vc", capture=True, rust_verify=ours, builtins=builtins)
            run_suite.stage_target_verus(tv, verus_src, args, label)
            self.assertEqual((tv / "rust_verify.real").read_text(), "ours")
            self.assertIn(str(tv / "rust_verify.real"), (tv / "rust_verify").read_text())

    def test_native_cli_outputs_are_staged_by_their_selected_bytes(self):
        with tempfile.TemporaryDirectory(prefix="tvs-stage-") as tmp:
            tmp = Path(tmp)
            builtins = tmp / "builtins"
            builtins.mkdir()
            for f in run_suite.BUILTIN_ARTIFACTS:
                (builtins / f).write_text(f)
            ours = tmp / "our_rust_verify"
            ours.write_text("ours")
            driver = tmp / "verus-driver"
            driver.write_text("#!/bin/sh\nexit 0\n")
            driver.chmod(0o755)
            item = {"path": str(driver), "sha256": run_suite.sha256(driver, {})}
            tv = tmp / "label/stage/source/target-verus/debug"
            tv.parent.mkdir(parents=True)
            args = stage_args("trust-vc", rust_verify=ours, builtins=builtins,
                              native_cli_inputs={"verus": item})
            staged = run_suite.stage_target_verus(tv, tmp / "verus/source", args, tmp / "label")
            self.assertEqual((tv / "verus").read_bytes(), driver.read_bytes())
            self.assertEqual(staged["verus"], item["sha256"])
            self.assertEqual(item["staged_path"], str(tv / "verus"))
            run_suite.check_native_cli_inputs(args.native_cli_inputs)

            driver.write_text("#!/bin/sh\nexit 1\n")
            with self.assertRaisesRegex(RuntimeError, "changed before staging"):
                run_suite.stage_target_verus(tv, tmp / "verus/source", args, tmp / "label")


class LedgerAndRefusalsTest(unittest.TestCase):
    def test_ledger_has_one_header(self):
        with tempfile.TemporaryDirectory(prefix="tvs-ledger-") as tmp:
            path = Path(tmp) / "runs.csv"
            tot = {o: 0 for o in run_suite.OUTCOMES}
            tot["ok"] = 3
            score = {"live": 3, "pass": 2, "refused": 1, "ok": True}
            for _ in range(2):
                run_suite.append_ledger(path, {"label": "l", "frontend": "trust-vc"}, tot,
                                        {"basic": {}}, score, Path("/ref"))
            with open(path, newline="") as f:
                rows = list(csv.DictReader(f))
            self.assertEqual(len(rows), 2)
            self.assertEqual((rows[0]["pass"], rows[0]["scored_ok"], rows[0]["ok"]), ("2", "True", "3"))

    def test_an_older_ledger_is_rewritten_under_the_current_header(self):
        with tempfile.TemporaryDirectory(prefix="tvs-ledger-") as tmp:
            path = Path(tmp) / "runs.csv"
            old_fields = [f for f in run_suite.LEDGER_FIELDS if f != "vacuous"]
            with open(path, "w", newline="") as f:
                w = csv.DictWriter(f, fieldnames=old_fields)
                w.writeheader()
                w.writerow({k: "7" if k == "false_pass" else "" for k in old_fields})
            tot = {o: 0 for o in run_suite.OUTCOMES}
            run_suite.append_ledger(path, {"label": "new"}, tot, {}, {"vacuous": 7, "ok": True}, None)
            with open(path, newline="") as f:
                reader = csv.DictReader(f)
                self.assertEqual(reader.fieldnames, run_suite.LEDGER_FIELDS)
                rows = list(reader)
            self.assertEqual([(r["false_pass"], r["vacuous"]) for r in rows], [("7", ""), ("", "7")])

    def test_runner_refuses_a_half_specified_trust_vc_run(self):
        with tempfile.TemporaryDirectory(prefix="tvs-refuse-") as tmp:
            base = [sys.executable, str(HERE / "run_suite.py"), "--out-root", tmp, "--label", "x",
                    "--frontend", "trust-vc"]
            r = subprocess.run(base, capture_output=True, text=True, timeout=120)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("--rust-verify and --builtins", r.stderr)
            r = subprocess.run(base + ["--solver", "/bin/true"], capture_output=True, text=True, timeout=120)
            self.assertIn("starts no solver process", r.stderr)
            self.assertFalse((Path(tmp) / "runs/x/stage").exists())


if __name__ == "__main__":
    unittest.main()
