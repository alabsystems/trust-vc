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
import csv
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
