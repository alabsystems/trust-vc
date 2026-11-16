#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Offline tests for the Verus-suite drivers and the committed reference set.

What is pinned here, and why:
  * AY_BIN has no default anywhere: run_suite.py (for the measurement shim),
    run_one.sh, split_rerun.sh and the re-run drivers refuse without it, with a
    clear message and a non-zero exit, before anything is staged or written. The re-run
    drivers refuse even when the run's run.json recorded a valid AY_BIN: a recorded path
    can hold another build by now. The old fallback pointed at a stale 0.26.0 build and
    silently measured the wrong solver.
  * the shell drivers parse, and run_one.sh refuses a stage that does not exist and a
    library directory without the exact librustc_driver the prebuilt binaries load;
  * run_one.sh passes every AY_SHIM_* and TOP3_* variable through to the test binary
    (ay's fix-simulation shim needs TOP3_Z3 and exits without it), keeps its own event
    and transcript directories, and never passes SHIM_SOLVER into an ay run. Checked
    with a fake stage whose "test binary" only writes its environment to a file;
  * every driver stops, with run_one.sh's message and a non-zero exit, when run_one.sh
    refuses, instead of writing a summary row for a test that never ran;
  * classify.py classifies a synthetic run and reads a committed reference that keeps
    only results.csv;
  * evals/verus/upstream-suite/ is self-consistent: the z3 reference has 4,213 tests,
    4,114 ok, and excluded-from-comparison.csv lists exactly the rest.
With VERUS_BASELINE_ROOT pointing at the recorded run tree of 2026-09-23, classify.py
must reproduce runs/ay-0919b4e16/classified.csv (and its three sibling outputs) byte
for byte, and denominator.py must reproduce denominator.csv (that part also needs the
Verus checkout and the rustc 1.95.0 toolchain; it is skipped without them). Outputs
go to a temporary directory; nothing is written under the recorded tree.
"""
from __future__ import annotations

import csv
import json
import os
import signal
import shlex
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from types import SimpleNamespace
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
SUITE = REPO / "evals" / "verus" / "upstream-suite"
sys.path.insert(0, str(HERE))
import suite_common  # noqa: E402
import run_suite  # noqa: E402


def clean_env(**extra):
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("AY_", "SHIM", "VERUS_SUITE_", "TOP3_"))}
    env.update({k: v for k, v in extra.items() if v is not None})
    return env


def read_csv(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))


def run(cmd, env=None, timeout=120):
    return subprocess.run([str(c) for c in cmd], capture_output=True, text=True, env=env or clean_env(),
                          timeout=timeout, stdin=subprocess.DEVNULL)


class RunnerCoverageTest(unittest.TestCase):
    """Actual driver fixtures; no Rust compiler, upstream harness or solver runs."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="verus-runner-coverage-")
        self.tmp = Path(self._tmp.name)
        self.src = self.tmp / "verus" / "source"
        self.deps = self.src / "target.noindex/debug/deps"
        self.deps.mkdir(parents=True)
        for root in run_suite.test_roots():
            (self.src / root).mkdir(parents=True)
        self.harness("rust_verify_test/tests/basic.rs", "basic")
        self.cargo = self.harness("cargo-verus/tests/test_build.rs", "test_build", cargo=True)
        self.lib = self.tmp / "lib"
        self.lib.mkdir()
        (self.lib / suite_common.RUSTC_DRIVER).touch()
        (self.src / "target-verus/debug").mkdir(parents=True)

    def tearDown(self):
        self._tmp.cleanup()

    def track_inputs(self):
        self.assertEqual(run(["git", "init", self.src.parent]).returncode, 0)
        self.assertEqual(run(["git", "-C", self.src.parent, "add", "."]).returncode, 0)

    def cargo_fixture(self):
        manifest = self.src / "rust_verify_test/tests/cargo-tests/verified/transitive3/Cargo.toml"
        manifest.parent.mkdir(parents=True)
        manifest.write_text('[package.metadata.verus]\ntest_ignore = true\n')
        (self.src / "vstd").mkdir()
        (self.src / "vstd/input.rs").write_text("source dependency")
        return manifest

    def harness(self, source, stem, cargo=False, frontend=False):
        (self.src / source).write_text("mod utils;\n" if cargo else "#[test] fn ordinary() {}\n")
        binary = self.deps / (stem + "-0123456789abcdef")
        stamp = self.tmp / (stem + ".executed")
        binary.write_text(f'''#!/bin/sh
exec {shlex.quote(sys.executable)} - "$@" <<'HARNESS_PYTHON'
import json, os, pathlib, subprocess, sys
names = {{"ordinary": False, "ignored_failure": True}}
if {stem == 'cargo'!r}: names["verified_transitive3"] = False
def event(**kw): print(json.dumps(kw), flush=True)
if "--list" in sys.argv:
    event(type="suite", event="discovery")
    for name, ignore in names.items(): event(type="test", event="discovered", name=name, ignore=ignore)
    event(type="suite", event="completed", tests=len(names), benchmarks=0, total=len(names), ignored=sum(names.values()))
else:
    pathlib.Path({str(stamp)!r}).write_text(pathlib.Path.cwd().name)
    failed = 0
    for name, ignore in names.items():
        if ignore and "--include-ignored" not in sys.argv:
            event(type="test", event="ignored", name=name); continue
        event(type="test", event="started", name=name)
        bad = (subprocess.run([str(pathlib.Path(os.environ["VARGO_TARGET_DIR"]) / "rust_verify")]).returncode != 0
               if {frontend!r} else ignore)
        outcome = "failed" if bad else "ok"
        event(type="test", event=outcome, name=name)
        failed += int(bad)
    event(type="suite", event="failed" if failed else "ok")
    sys.exit(bool(failed))
HARNESS_PYTHON
''')
        binary.chmod(0o755)
        if cargo:
            helpers = []
            for name in ("cargo-verus", "fake-cargo"):
                helper = self.tmp / "compiled helpers" / name
                helper.parent.mkdir(exist_ok=True)
                helper.write_text("#!/bin/sh\nexit 0\n")
                helper.chmod(0o755)
                helpers.append(f"# env-dep:CARGO_BIN_EXE_{name}={helper}\n")
            binary.with_suffix(".d").write_text("".join(helpers))
        return binary

    def test_discovery_keeps_first_root_ids_and_includes_second_root(self):
        bins, _ = run_suite.discover_binaries(self.src)
        self.assertEqual(set(bins), {"basic", "cargo-verus.test_build"})
        self.assertEqual(run_suite.binary_source("basic"), Path("rust_verify_test/tests/basic.rs"))
        self.assertEqual(run_suite.binary_cwd("cargo-verus.test_build", self.src), self.src / "cargo-verus")
        self.cargo.unlink()
        with self.assertRaisesRegex(SystemExit, "cargo-verus.test_build"):
            run_suite.discover_binaries(self.src)

    def test_ambiguous_source_and_duplicate_binary_fail_closed(self):
        (self.src / "cargo-verus/tests/basic.rs").touch()
        with self.assertRaisesRegex(SystemExit, "ambiguous upstream test target basic"):
            run_suite.discover_binaries(self.src)
        (self.src / "cargo-verus/tests/basic.rs").unlink()
        duplicate = self.deps / "basic-fedcba9876543210"
        duplicate.write_text("#!/bin/sh\n")
        duplicate.chmod(0o755)
        with self.assertRaisesRegex(SystemExit, "two binaries for basic"):
            run_suite.discover_binaries(self.src)

    def test_compiled_helpers_are_real_paths_and_missing_or_changed_refuses(self):
        source = self.src / "cargo-verus/tests/test_build.rs"
        record = run_suite.cargo_helpers(self.cargo, source)
        self.assertEqual(set(record["helpers"]), {"cargo-verus", "fake-cargo"})
        run_suite.check_cargo_helpers(record)
        helper = Path(record["helpers"]["fake-cargo"]["path"])
        helper.write_text("changed")
        with self.assertRaisesRegex(RuntimeError, "helper changed"):
            run_suite.check_cargo_helpers(record)
        helper.unlink()
        with self.assertRaisesRegex(SystemExit, "not executable"):
            run_suite.cargo_helpers(self.cargo, source)

    def test_include_ignored_really_executes_and_preserves_failure(self):
        binary = self.deps / "basic-0123456789abcdef"
        discovery = run_suite.list_tests(binary, dict(os.environ), self.src / "rust_verify_test")
        args = SimpleNamespace(bin_wall=10, max_attempts=1, threads=2, test_stall=5, include_ignored=True)
        result = run_suite.run_binary("basic", binary, dict(os.environ), self.src / "rust_verify_test",
                                      args, self.tmp, discovery)
        self.assertEqual(set(result["results"]), set(discovery))
        self.assertEqual(result["results"]["ignored_failure"]["outcome"], "FAILED")
        self.assertEqual((self.tmp / "basic.executed").read_text(), "rust_verify_test")

    def test_missing_recorded_case_is_not_dropped_from_reports(self):
        label = self.tmp / "label"
        (label / "bins").mkdir(parents=True)
        (label / "bins/basic.json").write_text(json.dumps({
            "discovery": {"ordinary": {}, "ignored_failure": {"ignore": True}},
            "results": {"ordinary": {"outcome": "ok"}},
        }))
        rows, _ = run_suite.load_results(label, {"basic": None}, {}, {})
        self.assertEqual({r["test_name"]: r["outcome"] for r in rows},
                         {"ordinary": "ok", "ignored_failure": "not-run"})

    def test_discovery_rejects_partial_duplicate_and_non_json_output(self):
        for body in [
            'print("discovery")',
            'print(\'{"type":"suite","event":"discovery"}\')',
            'print(\'{"type":"suite","event":"discovery"}\'); '
            'print(\'{"type":"test","event":"discovered","name":"one"}\'); '
            'print(\'{"type":"suite","event":"completed","tests":2,"benchmarks":0,"total":2,"ignored":0}\')',
            'print(\'{"type":"suite","event":"discovery"}\'); '
            'print(\'{"type":"test","event":"discovered","name":"one"}\'); '
            'print(\'{"type":"test","event":"discovered","name":"one"}\')',
        ]:
            binary = self.tmp / "bad-list"
            binary.write_text(f"#!/bin/sh\nexec {shlex.quote(sys.executable)} -c {shlex.quote(body)}\n")
            binary.chmod(0o755)
            with self.assertRaises(RuntimeError):
                run_suite.list_tests(binary, dict(os.environ), self.tmp)

    def test_cargo_stage_is_independent_and_records_internal_skip(self):
        manifest = self.cargo_fixture()
        self.track_inputs()
        root = self.tmp / "stage"
        (root / "source").mkdir(parents=True)
        (root / "source/vstd").symlink_to(self.src / "vstd")
        run_suite.stage_cargo_sources(root, self.src)
        copied = root / manifest.relative_to(self.src.parent)
        self.assertEqual(copied.read_text(), manifest.read_text())
        copied.write_text("changed by Cargo")
        (root / "source/vstd/input.rs").write_text("changed dependency")
        self.assertIn("test_ignore = true", manifest.read_text())
        self.assertEqual((self.src / "vstd/input.rs").read_text(), "source dependency")
        self.assertEqual(set(run_suite.cargo_internal_skips(self.src)), {"verified_transitive3"})

    def test_captured_discovery_keeps_ignored_names_and_rejects_failed_exit(self):
        stdout = "\n".join(json.dumps(row) for row in [
            {"type": "suite", "event": "discovery"},
            {"type": "test", "event": "discovered", "name": "ignored_case", "ignore": True},
            {"type": "suite", "event": "completed", "tests": 1, "benchmarks": 0, "total": 1, "ignored": 1},
        ])
        self.assertEqual(run_suite.parse_discovery(stdout, 0, "captured"),
                         {"ignored_case": {"ignore": True, "source_path": "", "line": ""}})
        with self.assertRaisesRegex(RuntimeError, "rc=1"):
            run_suite.parse_discovery(stdout, 1, "captured", "actual failed exit")

    def test_full_suite_executes_both_roots_and_rejects_legacy_cache_policy(self):
        self.harness("rust_verify_test/tests/cargo.rs", "cargo")
        self.cargo_fixture()
        self.track_inputs()
        out = self.tmp / "out"
        cmd = [sys.executable, HERE / "run_suite.py", "--solver", "/usr/bin/true", "--label", "full",
               "--out-root", out, "--verus", self.src.parent, "--dyld", self.lib,
               "--full-suite", "--include-ignored", "--max-attempts", "1"]
        p = run(cmd, timeout=30)
        self.assertEqual(p.returncode, 1, p.stdout + p.stderr)  # both real fixture failures are retained
        self.assertTrue((out / "runs/full/results.csv").exists(), p.stdout + p.stderr)
        rows = read_csv(out / "runs/full/results.csv")
        self.assertEqual({(r["binary"], r["test_name"]) for r in rows},
                         {(b, t) for b in ("basic", "cargo", "cargo-verus.test_build")
                          for t in ("ordinary", "ignored_failure")} | {("cargo", "verified_transitive3")})
        skipped = next(r for r in rows if r["test_name"] == "verified_transitive3")
        self.assertIn("body returns before Cargo", skipped["coverage_note"])
        self.assertEqual(sum(r["outcome"] == "FAILED" for r in rows), 3)
        self.assertEqual((self.tmp / "test_build.executed").read_text(), "cargo-verus")
        # Even a same-policy cache explicitly marked excluded is not execution evidence.
        cached = out / "runs/full/bins/basic.json"
        old = json.loads(cached.read_text())
        old["excluded"] = True
        old["results"]["ignored_failure"]["outcome"] = "ok"
        cached.write_text(json.dumps(old))
        (self.tmp / "basic.executed").unlink()
        rerun = run(cmd, timeout=30)
        self.assertEqual(rerun.returncode, 1, rerun.stdout + rerun.stderr)
        self.assertTrue((self.tmp / "basic.executed").exists())
        self.assertEqual(json.loads(cached.read_text())["results"]["ignored_failure"]["outcome"], "FAILED")
        meta = out / "runs/full/run.json"
        data = json.loads(meta.read_text())
        data["coverage_policy"]["include_ignored"] = False
        meta.write_text(json.dumps(data))
        refused = run(cmd, timeout=30)
        self.assertIn("coverage policy changed", refused.stderr)

    def test_full_suite_reruns_cached_passes_when_frontend_changes(self):
        self.harness("rust_verify_test/tests/basic.rs", "basic", frontend=True)
        self.harness("cargo-verus/tests/test_build.rs", "test_build", cargo=True, frontend=True)
        driver = self.src / "target-verus/debug/rust_verify"
        driver.write_text("#!/bin/sh\nexit 0\n")
        driver.chmod(0o755)
        cmd = [sys.executable, HERE / "run_suite.py", "--solver", "/usr/bin/true", "--label", "fresh",
               "--out-root", self.tmp / "out", "--verus", self.src.parent, "--dyld", self.lib,
               "--full-suite", "--include-ignored", "--max-attempts", "1"]
        first = run(cmd, timeout=30)
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        results = self.tmp / "out/runs/fresh/results.csv"
        self.assertEqual([r["outcome"] for r in read_csv(results)], ["ok"] * 4)
        driver.write_text("#!/bin/sh\nexit 1\n")
        for stem in ("basic", "test_build"):
            (self.tmp / (stem + ".executed")).unlink()
        second = run(cmd, timeout=30)
        self.assertEqual(second.returncode, 1, second.stdout + second.stderr)
        self.assertEqual([r["outcome"] for r in read_csv(results)], ["FAILED"] * 4)
        for stem in ("basic", "test_build"):
            self.assertTrue((self.tmp / (stem + ".executed")).exists())

    def test_native_cargo_pair_is_required_only_for_selected_cargo_cases(self):
        args = SimpleNamespace(frontend="trust-vc", verus_driver=None, cargo_verus=None)
        self.assertEqual(run_suite.native_cli_inputs(args, {"basic": self.cargo}), {})
        self.assertEqual(run_suite.native_cli_inputs(args, {"cargo-verus.test_build": self.cargo}), {})
        with self.assertRaisesRegex(SystemExit, "cargo harness needs"):
            run_suite.native_cli_inputs(args, {"cargo": self.cargo})
        args.verus_driver = self.cargo
        with self.assertRaisesRegex(SystemExit, "supplied together"):
            run_suite.native_cli_inputs(args, {})
        args.frontend = "verus"
        with self.assertRaisesRegex(SystemExit, "trust-vc only"):
            run_suite.native_cli_inputs(args, {})

    def test_native_cargo_stage_keeps_sibling_lookup_and_checks_both_copies(self):
        outputs = self.tmp / "native outputs"
        outputs.mkdir()
        for name in ("rust_verify", "verus", "cargo-verus"):
            file = outputs / name
            # Runner fixture only; actual native binaries need their own Rust run.
            file.write_text("#!/bin/sh\nexit 0\n")
            file.chmod(0o755)
        builtins = outputs / "builtins"
        builtins.mkdir()
        for name in run_suite.BUILTIN_ARTIFACTS:
            (builtins / name).write_text(name)
        args = SimpleNamespace(frontend="trust-vc", capture_diagnostics=False,
                               rust_verify=outputs / "rust_verify", builtins=builtins,
                               verus_driver=outputs / "verus", cargo_verus=outputs / "cargo-verus")
        args.native_cli_inputs = run_suite.native_cli_inputs(args, {"cargo": self.cargo})
        target = self.tmp / "stage target"
        staged = run_suite.stage_target_verus(target, self.src, args, self.tmp)
        self.assertEqual(set(staged), set(run_suite.BUILTIN_ARTIFACTS) |
                         {"rust_verify", "verus", "cargo-verus"})
        for name in ("verus", "cargo-verus"):
            self.assertEqual((target / name).read_bytes(), (outputs / name).read_bytes())
        self.assertFalse((target / "libvstd.rlib").exists())
        self.assertFalse((target / "vstd.vir").exists())
        run_suite.check_native_cli_inputs(args.native_cli_inputs)
        (target / "verus").write_text("stage changed")
        with self.assertRaisesRegex(RuntimeError, "native CLI build output changed"):
            run_suite.check_native_cli_inputs(args.native_cli_inputs)
        (target / "verus").write_bytes((outputs / "verus").read_bytes())
        (outputs / "cargo-verus").write_text("source changed")
        with self.assertRaisesRegex(RuntimeError, "native CLI build output changed"):
            run_suite.check_native_cli_inputs(args.native_cli_inputs)

    def test_native_children_keep_cargo_context_and_broker_caps(self):
        args = SimpleNamespace(frontend="trust-vc", dyld=self.lib, label_dir=self.tmp,
                               verus_extra_args="", env=[])
        values = {"CARGO": "/actual/targo", "RUSTC": "/actual/trustc",
                  "CARGO_HOME": "/own/home", "CARGO_TARGET_DIR": "/own/target",
                  "CARGO_BUILD_JOBS": "5", "BUILD_SLOT_CPU_BUDGET": "6",
                  "BUILD_SLOT_HELD": "1", "BUILD_SLOT_CPU_PROTOCOL": "1",
                  "TARGO_CALLER_JOBS": "5", "TARGO_PLANNED_JOBS": "6",
                  "RUSTC_BOOTSTRAP": "1", "RUSTC_WRAPPER": "/must-not-inherit",
                  "UNRELATED_SECRET_FIXTURE": "not a run input"}
        with patch.dict(os.environ, values, clear=True):
            env = run_suite.child_env(args, self.src)
        for key, value in values.items():
            if key not in ("UNRELATED_SECRET_FIXTURE", "RUSTC_BOOTSTRAP", "RUSTC_WRAPPER"):
                self.assertEqual(env[key], value)
        self.assertNotIn("UNRELATED_SECRET_FIXTURE", env)
        self.assertNotIn("RUSTC_BOOTSTRAP", env)
        self.assertNotIn("RUSTC_WRAPPER", env)
        self.assertEqual(env["VERUS_Z3_PATH"], run_suite.NO_SOLVER)

    def test_native_children_cannot_replace_the_compiler_context(self):
        args = SimpleNamespace(frontend="trust-vc", dyld=self.lib, label_dir=self.tmp,
                               verus_extra_args="", env=[])
        with patch.dict(os.environ, {}, clear=True):
            self.assertNotIn("RUSTC", run_suite.child_env(args, self.src))
        with patch.dict(os.environ, {"RUSTC": "/actual/trustc"}, clear=True):
            for key, value in (
                ("RUSTC_BOOTSTRAP", "1"), ("RUSTC", "/replacement/trustc"),
                ("RUSTC", "/actual/trustc"), ("RUSTC_WRAPPER", "/wrapper"),
                ("rustc_bootstrap", "1"), ("Rustc", "/replacement/trustc"),
                ("RUSTC_WORKSPACE_WRAPPER", "/wrapper"),
                ("CARGO_BUILD_RUSTC", "/replacement/trustc"),
                ("CARGO_BUILD_RUSTC_WRAPPER", "/wrapper"),
                ("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "/wrapper"),
            ):
                args.env = [key + "=" + value]
                with self.subTest(key=key, value=value):
                    with self.assertRaisesRegex(SystemExit, "inherited unchanged"):
                        run_suite.child_env(args, self.src)

    def test_original_verus_children_keep_the_reference_compiler_setup(self):
        args = SimpleNamespace(frontend="verus", dyld=self.lib, label_dir=self.tmp,
                               solver=self.tmp / "z3", verus_extra_args="", env=[])
        with patch.dict(os.environ, {"RUSTC": "/original/compiler"}, clear=True):
            env = run_suite.child_env(args, self.src)
            self.assertEqual(env["RUSTC_BOOTSTRAP"], "1")
            self.assertEqual(env["RUSTC"], "/original/compiler")
            self.assertEqual(env["VERUS_Z3_PATH"], str(args.solver.absolute()))
            args.env = ["RUSTC=/reference/override", "RUSTC_BOOTSTRAP=reference-value"]
            env = run_suite.child_env(args, self.src)
            self.assertEqual(env["RUSTC"], "/reference/override")
            self.assertEqual(env["RUSTC_BOOTSTRAP"], "reference-value")

    def test_nested_targo_locator_is_data_and_cannot_be_injected_or_replaced(self):
        args = SimpleNamespace(frontend="trust-vc", dyld=self.lib, label_dir=self.tmp,
                               verus_extra_args="", env=[])
        name = run_suite.TARGO_NESTED_ENDPOINT
        legacy = run_suite.TARGO_LEGACY_ENDPOINT
        # This fixture checks byte transport only, never live authorization.
        with patch.dict(os.environ, {name: "inert-locator-fixture", legacy: "obsolete"}, clear=True):
            child = run_suite.child_env(args, self.src)
        self.assertEqual(child[name], "inert-locator-fixture")
        self.assertNotIn(legacy, child)
        with patch.dict(os.environ, {}, clear=True):
            self.assertNotIn(name, run_suite.child_env(args, self.src))
            for forbidden in (name, legacy):
                args.env = [forbidden + "=injected"]
                with self.assertRaisesRegex(SystemExit, "inherited unchanged"):
                    run_suite.child_env(args, self.src)

    def test_native_epoch_refuses_before_staging_or_starting_a_harness(self):
        read_fd, write_fd = os.pipe()
        try:
            # Real live descriptors still cannot supply Targo's private owned
            # handoff capsule through an unmodified upstream libtest.
            native = dict(os.environ, BUILD_SLOT_CPU_PROTOCOL="2",
                          BUILD_SLOT_FENCE_FDS=f"{read_fd},{write_fd}")
            args = SimpleNamespace(frontend="verus", capture_diagnostics=False)
            target = self.tmp / "must-not-stage"
            with patch.dict(os.environ, native, clear=True):
                with self.assertRaisesRegex(SystemExit, "native CPU epochs"):
                    run_suite.stage_target_verus(target, self.src, args, self.tmp)
            self.assertFalse(target.exists())
            binary = self.deps / "basic-0123456789abcdef"
            with self.assertRaisesRegex(SystemExit, "native CPU epochs"):
                run_suite.list_tests(binary, native, self.tmp)
            with self.assertRaisesRegex(SystemExit, "native CPU epochs"):
                run_suite.run_attempt(binary, None, native, self.tmp, 1, 1, 1,
                                      self.tmp / "must-not-run", 1)
            self.assertFalse((self.tmp / "basic.executed").exists())
            self.assertFalse(list(self.tmp.glob("must-not-run.*")))
            os.fstat(read_fd)
            os.fstat(write_fd)
            # A conflicting protocol string cannot downgrade live-fence input.
            native["BUILD_SLOT_CPU_PROTOCOL"] = "1"
            with self.assertRaisesRegex(SystemExit, "native CPU epochs"):
                run_suite.list_tests(binary, native, self.tmp)
        finally:
            os.close(read_fd)
            os.close(write_fd)

    def lender_fixture(self):
        lender = self.tmp / "lender with ' spaces"
        # This fixture merely execs argv. It grants no GNU or CPU authority.
        lender.write_text('#!/bin/bash\nexec "$@"\n')
        lender.chmod(0o755)
        return lender

    def lending_args(self, lender):
        return SimpleNamespace(frontend="trust-vc", execution_lender=lender,
                               threads=1, parallel_bins=1, env=[])

    def test_execution_lender_refuses_context_before_filtering_or_staging(self):
        args = self.lending_args(self.lender_fixture())
        fixed = {"BUILD_SLOT_HELD": "1", "BUILD_SLOT_CPU_PROTOCOL": "1"}
        for extra in ({}, {"BUILD_SLOT_CPU_PROTOCOL": "2"}):
            values = {} if not extra else dict(fixed, **extra)
            with patch.dict(os.environ, values, clear=True):
                with self.assertRaisesRegex(SystemExit, "fixed build-slot"):
                    run_suite.execution_lender_inputs(args)
        for key in run_suite.LENDER_ADVERTISEMENTS:
            # Even an empty advertisement must not be erased by the allowlist.
            with patch.dict(os.environ, dict(fixed, **{key: ""}), clear=True):
                with self.assertRaisesRegex(SystemExit, "advertised custody"):
                    run_suite.execution_lender_inputs(args)
        with patch.dict(os.environ, fixed, clear=True):
            for key in ("BUILD_SLOT_CPU_PROTOCOL", "CARGO_MAKEFLAGS", "CARGO_BUILD_JOBS",
                        "TRUST_CPU_HANDOFF", "ATERM_SDK_LEASE_V3"):
                args.env = [key + "=injected"]
                with self.assertRaisesRegex(SystemExit, "admission context"):
                    run_suite.execution_lender_inputs(args)
            args.env = []
            args.threads = 2
            with self.assertRaisesRegex(SystemExit, "threads 1"):
                run_suite.execution_lender_inputs(args)
            args.threads, args.parallel_bins = 1, 2
            with self.assertRaisesRegex(SystemExit, "parallel-bins 1"):
                run_suite.execution_lender_inputs(args)
            args.frontend = "verus"
            with self.assertRaisesRegex(SystemExit, "trust-vc only"):
                run_suite.execution_lender_inputs(args)

    def test_execution_wrapper_preserves_argv_bytes_exit_and_signal_with_capture(self):
        lender = self.lender_fixture()
        body = self.tmp / "driver with ' spaces.py"
        body.write_text('''import json, os, signal, sys
print(json.dumps(sys.argv[2:]), flush=True)
print("original stderr", file=sys.stderr, flush=True)
if sys.argv[1].startswith("signal:"):
    sig = int(sys.argv[1].partition(":")[2])
    if sig not in (signal.SIGKILL, signal.SIGSTOP):
        signal.signal(sig, signal.SIG_DFL)
    signal.pthread_sigmask(signal.SIG_UNBLOCK, [sig])
    os.kill(os.getpid(), sig)
sys.exit(int(sys.argv[1]))
''')
        fixed = {"BUILD_SLOT_HELD": "1", "BUILD_SLOT_CPU_PROTOCOL": "1"}
        payload = ["a b", "'literal\"", "$(not executed)", "semi;colon", "unicode-λ"]
        for capture in (False, True):
            wrapper = self.tmp / ("capture wrapper" if capture else "exec wrapper")
            diags = self.tmp / "captured diagnostics" if capture else None
            run_suite.stage_execution_wrapper(wrapper, Path(sys.executable), lender,
                                              self.lib, diags)
            for status in (0, 7, 139):
                result = run([wrapper, "-I", "-S", body, status, *payload,
                              "-o", self.tmp / "actual output" / "out"], env=fixed)
                self.assertEqual(result.returncode, status, result)
                self.assertEqual(json.loads(result.stdout), payload + ["-o", str(self.tmp / "actual output" / "out")])
                self.assertEqual(result.stderr, "original stderr\n")
            for sig in (signal.SIGTERM, signal.SIGUSR1, signal.SIGKILL):
                result = run([wrapper, "-I", "-S", body, "signal:" + str(sig), *payload], env=fixed)
                self.assertEqual(result.returncode, -sig, result)
                self.assertEqual(result.stderr, "original stderr\n")
            if capture:
                files = list((diags / "actual output").glob("*.stderr"))
                self.assertEqual(len(files), 3)
                self.assertTrue(any(path.read_text().endswith("exit=139\n") for path in files))
                def ignore_and_block():
                    signal.signal(signal.SIGUSR1, signal.SIG_IGN)
                    signal.pthread_sigmask(signal.SIG_BLOCK, [signal.SIGUSR1])
                inherited = subprocess.run(
                    [str(wrapper), "-I", "-S", str(body), "signal:" + str(signal.SIGUSR1)],
                    env=fixed, capture_output=True, timeout=30, preexec_fn=ignore_and_block)
                self.assertEqual(inherited.returncode, -signal.SIGUSR1, inherited)
            refused = run([wrapper, "-I", "-S", body, 0], env=dict(fixed, MAKEFLAGS=""))
            self.assertEqual(refused.returncode, 75)
            self.assertEqual(refused.stdout, "")

    def test_execution_lender_stage_keeps_real_images_and_detects_tampering(self):
        outputs = self.tmp / "native lending inputs"
        outputs.mkdir()
        for name in ("rust_verify", "verus", "cargo-verus"):
            file = outputs / name
            file.write_text("#!/bin/bash\nexit 0\n")
            file.chmod(0o755)
        builtins = outputs / "builtins"
        builtins.mkdir()
        for name in run_suite.BUILTIN_ARTIFACTS:
            (builtins / name).write_text(name)
        args = self.lending_args(self.lender_fixture())
        args.capture_diagnostics = True
        args.rust_verify, args.verus_driver = outputs / "rust_verify", outputs / "verus"
        args.cargo_verus, args.builtins, args.dyld = outputs / "cargo-verus", builtins, self.lib
        fixed = {"BUILD_SLOT_HELD": "1", "BUILD_SLOT_CPU_PROTOCOL": "1"}
        with patch.dict(os.environ, fixed, clear=True):
            args.execution_lender_inputs = run_suite.execution_lender_inputs(args)
            args.native_cli_inputs = run_suite.native_cli_inputs(args, {"cargo": self.cargo})
            target = self.tmp / "lending stage"
            staged = run_suite.stage_target_verus(target, self.src, args, self.tmp)
        for name in ("rust_verify", "verus"):
            self.assertEqual((target / (name + ".real")).read_bytes(), (outputs / name).read_bytes())
            self.assertIn(name, staged)
            self.assertIn(name + ".execution.py", staged)
        self.assertEqual((target / "cargo-verus").read_bytes(), args.cargo_verus.read_bytes())
        self.assertEqual(args.native_cli_inputs["verus"]["staged_path"], str(target / "verus.real"))
        run_suite.check_native_cli_inputs(args.native_cli_inputs)
        pins = run_suite.native_runtime.snapshot_files(target / name for name in staged)
        (target / "execution-lender").write_text("changed staged lender")
        with self.assertRaisesRegex(RuntimeError, "input changed"):
            run_suite.native_runtime.check_files(pins)
        args.execution_lender.write_text("changed original lender")
        with self.assertRaisesRegex(RuntimeError, "input changed"):
            run_suite.native_runtime.check_files(args.execution_lender_inputs)

    def test_full_suite_requires_ignored_execution_before_writing(self):
        out = self.tmp / "out"
        p = run([sys.executable, HERE / "run_suite.py", "--label", "full", "--out-root", out, "--full-suite"])
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("requires --include-ignored", p.stderr)
        self.assertFalse(out.exists())
        p = run([sys.executable, HERE / "run_suite.py", "--label", "full", "--out-root", out,
                 "--full-suite", "--include-ignored", "--summarize-only"])
        self.assertNotEqual(p.returncode, 0)
        self.assertIn("forbids", p.stderr)
        self.assertFalse(out.exists())


class AyBinRequiredTest(unittest.TestCase):
    """(d) every driver that runs ay refuses without AY_BIN, before writing anything."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="verus-suite-harness-")
        self.tmp = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def assert_refused(self, p, needle="AY_BIN"):
        self.assertNotEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn(needle, p.stderr)
        self.assertNotIn("Traceback", p.stderr)

    def test_run_suite_with_the_shim(self):
        p = run([sys.executable, HERE / "run_suite.py", "--solver", HERE / "ay_z3shim.py", "--label", "t",
                 "--out-root", self.tmp / "out", "--verus", self.tmp / "no-verus"])
        self.assert_refused(p, "--env AY_BIN=")
        self.assertFalse((self.tmp / "out").exists(), "refused, yet something was written")

    def test_run_suite_with_a_bad_ay_bin(self):
        p = run([sys.executable, HERE / "run_suite.py", "--solver", HERE / "ay_z3shim.py", "--label", "t",
                 "--out-root", self.tmp / "out", "--verus", self.tmp / "no-verus",
                 "--env", f"AY_BIN={self.tmp / 'missing'}"])
        self.assert_refused(p, "is not an executable file")
        self.assertFalse((self.tmp / "out").exists())

    def test_run_suite_shim_z3_passthrough_needs_no_ay_bin(self):
        # gets past the AY_BIN preflight and stops at the missing Verus checkout instead
        p = run([sys.executable, HERE / "run_suite.py", "--solver", HERE / "ay_z3shim.py", "--label", "t",
                 "--out-root", self.tmp / "out", "--verus", self.tmp / "no-verus",
                 "--dyld", self.tmp, "--env", "SHIM_SOLVER=z3:/bin/false"])
        self.assertNotEqual(p.returncode, 0)
        self.assertNotIn("AY_BIN", p.stderr)

    def test_run_one(self):
        out = self.tmp / "one"
        p = run([HERE / "run_one.sh", "z3-shim", "ay", out, "basic", "test1"],
                env=clean_env(VERUS_SUITE_OUT_ROOT=str(self.tmp / "root")))
        self.assert_refused(p)
        self.assertFalse(out.exists())

    def test_split_rerun(self):
        p = run([HERE / "split_rerun.sh", "ay-x"], env=clean_env(VERUS_SUITE_OUT_ROOT=str(self.tmp / "root")))
        self.assert_refused(p)
        self.assertFalse((self.tmp / "root").exists())

    def test_run_tests_with_shim(self):
        tests = self.tmp / "tests.txt"
        tests.write_text("basic::test1\n")
        p = run([sys.executable, HERE / "run_tests_with_shim.py", "--tests-file", tests, "--out", self.tmp / "o",
                 "--out-root", self.tmp / "root"])
        self.assert_refused(p)
        self.assertFalse((self.tmp / "o").exists())

    def test_confirm_soundness(self):
        p = run([sys.executable, HERE / "confirm_soundness.py", "--label", "x", "--out-root", self.tmp / "root"])
        self.assert_refused(p)

    def recorded_run(self, env):
        run_dir = self.tmp / "root" / "runs" / "ay-x"
        run_dir.mkdir(parents=True)
        (run_dir / "run.json").write_text(json.dumps({"invocations": [{"env": env}]}))
        (run_dir / "classified.csv").write_text("class,subclass,binary,test_name,query_hash\n")

    def test_rerun_drivers_never_use_the_recorded_ay_bin(self):
        # the recorded AY_BIN is a real executable, and still it is not taken
        self.recorded_run({"AY_BIN": sys.executable})
        for script in ("rerun_tests.py", "rerun_timeouts.py"):
            with self.subTest(script=script):
                p = run([sys.executable, HERE / script, "--label", "ay-x", "--out", self.tmp / "o",
                         "--out-root", self.tmp / "root"])
                self.assert_refused(p, "AY_BIN is required")
                self.assertFalse((self.tmp / "o").exists(), "refused, yet something was written")

    def test_rerun_drivers_with_a_missing_ay_bin(self):
        self.recorded_run({})
        for script in ("rerun_tests.py", "rerun_timeouts.py"):
            with self.subTest(script=script):
                p = run([sys.executable, HERE / script, "--label", "ay-x", "--out", self.tmp / "o",
                         "--out-root", self.tmp / "root", "--ay-bin", self.tmp / "gone"])
                self.assert_refused(p, "is not an executable file")


class RunOneRefusalStopsTheDriversTest(unittest.TestCase):
    """A run_one.sh refusal (here: no stage under the out root) stops every driver with
    run_one.sh's message. Nothing runs a test binary or a solver: run_one.sh refuses
    before it launches anything."""

    INCOMPLETE = "no answer within the wall where z3 proved unsat"

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="verus-suite-refusal-")
        self.tmp = Path(self._tmp.name)
        self.root = self.tmp / "root"
        run_dir = self.root / "runs" / "ay-x"
        run_dir.mkdir(parents=True)
        (run_dir / "run.json").write_text(json.dumps({"invocations": [{"env": {}}]}))
        with open(run_dir / "classified.csv", "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=["class", "subclass", "binary", "test_name", "query_hash",
                                              "query_index", "ay_answer", "z3_answer"])
            w.writeheader()
            w.writerow({"class": "INCOMPLETE", "subclass": self.INCOMPLETE, "binary": "basic",
                        "test_name": "test1", "query_hash": "h", "query_index": "0", "ay_answer": "",
                        "z3_answer": "unsat"})
            w.writerow({"class": "SOUNDNESS", "subclass": "x", "binary": "basic", "test_name": "test2",
                        "query_hash": "h2", "query_index": "0", "ay_answer": "unsat", "z3_answer": "sat"})

    def tearDown(self):
        self._tmp.cleanup()

    def assert_stopped(self, p, summary=None):
        self.assertNotEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertIn("no stage at", p.stderr)
        self.assertNotIn("Traceback", p.stderr)
        if summary is not None:
            self.assertFalse(summary.exists(), f"{summary} was written for tests that never ran")

    def test_rerun_tests(self):
        p = run([sys.executable, HERE / "rerun_tests.py", "--label", "ay-x", "--out", self.tmp / "o",
                 "--out-root", self.root, "--ay-bin", sys.executable, "--tests", "basic::test1"])
        self.assert_stopped(p, self.tmp / "o" / "summary.csv")

    def test_rerun_timeouts(self):
        p = run([sys.executable, HERE / "rerun_timeouts.py", "--label", "ay-x", "--out", self.tmp / "o",
                 "--out-root", self.root, "--ay-bin", sys.executable])
        self.assert_stopped(p, self.tmp / "o" / "summary.csv")

    def test_run_tests_with_shim(self):
        tests = self.tmp / "tests.txt"
        tests.write_text("basic::test1\nbasic::test2\n")
        p = run([sys.executable, HERE / "run_tests_with_shim.py", "--tests-file", tests, "--out", self.tmp / "o",
                 "--out-root", self.root], env=clean_env(AY_BIN=sys.executable))
        self.assert_stopped(p, self.tmp / "o" / "summary.csv")

    def test_confirm_soundness(self):
        verus = self.tmp / "verus"
        (verus / "source" / "rust_verify_test" / "tests").mkdir(parents=True)
        p = run([sys.executable, HERE / "confirm_soundness.py", "--label", "ay-x", "--out-root", self.root,
                 "--ay-bin", sys.executable, "--verus", verus])
        self.assert_stopped(p, self.root / "soundness-confirmations.json")

    def test_split_rerun(self):
        p = run([HERE / "split_rerun.sh", "ay-x"],
                env=clean_env(VERUS_SUITE_OUT_ROOT=str(self.root), AY_BIN=sys.executable))
        self.assertEqual(p.returncode, 2, p.stdout + p.stderr)
        self.assert_stopped(p)


class ShellDriverTest(unittest.TestCase):
    def test_shell_syntax(self):
        for script in ("run_one.sh", "split_rerun.sh"):
            with self.subTest(script=script):
                p = run(["bash", "-n", HERE / script])
                self.assertEqual(p.returncode, 0, p.stderr)

    def test_run_one_needs_a_stage(self):
        with tempfile.TemporaryDirectory(prefix="verus-suite-harness-") as tmp:
            p = run([HERE / "run_one.sh", "nolabel", "ay", Path(tmp) / "one", "basic", "test1"],
                    env=clean_env(VERUS_SUITE_OUT_ROOT=tmp, AY_BIN=sys.executable))
            self.assertEqual(p.returncode, 2, p.stderr)
            self.assertIn("no stage at", p.stderr)

    def test_run_one_rejects_an_unknown_solver(self):
        p = run([HERE / "run_one.sh", "z3-shim", "cvc5", "/nonexistent/out", "basic", "test1"])
        self.assertEqual(p.returncode, 2)
        self.assertIn("solver must be ay or z3", p.stderr)

    def fake_stage(self, tmp):
        """An out root whose stage 'lbl' has a 'test binary' that only writes its environment
        to a file; a library directory holding (an empty file named like) the exact driver."""
        root, dump = tmp / "root", tmp / "env.txt"
        stage = root / "runs" / "lbl" / "stage" / "source"
        (stage / "rust_verify_test").mkdir(parents=True)
        deps = stage / "target.noindex" / "debug" / "deps"
        deps.mkdir(parents=True)
        fake = deps / "fakebin"
        fake.write_text(f"#!/bin/sh\nenv > '{dump}'\n")
        fake.chmod(0o755)
        lib = tmp / "lib"
        lib.mkdir()
        (lib / suite_common.RUSTC_DRIVER).write_bytes(b"")
        return root, lib, dump

    def test_run_one_passes_every_shim_setting_through(self):
        with tempfile.TemporaryDirectory(prefix="verus-suite-harness-") as tmp:
            tmp = Path(tmp)
            root, lib, dump = self.fake_stage(tmp)
            out = tmp / "one"
            p = run([HERE / "run_one.sh", "lbl", "ay", out, "fakebin", "t1"],
                    env=clean_env(VERUS_SUITE_OUT_ROOT=str(root), VERUS_SUITE_DYLD=str(lib),
                                  AY_BIN=sys.executable, SHIM="/some/ay-z3shim-top3",
                                  TOP3_Z3="/some/z3", TOP3_ORACLE="DM", AY_SHIM_EOF_GRACE_S="7",
                                  AY_SHIM_NOT_YET_INVENTED="x y", AY_SHIM_EVENT_DIR="/elsewhere/events",
                                  SHIM_SOLVER="z3:/some/z3"))
            self.assertEqual(p.returncode, 0, p.stderr)
            env = dict(line.split("=", 1) for line in dump.read_text().splitlines() if "=" in line)
            self.assertEqual(env.get("TOP3_Z3"), "/some/z3")
            self.assertEqual(env.get("TOP3_ORACLE"), "DM")
            self.assertEqual(env.get("AY_SHIM_EOF_GRACE_S"), "7")
            self.assertEqual(env.get("AY_SHIM_NOT_YET_INVENTED"), "x y")
            self.assertEqual(env.get("VERUS_Z3_PATH"), "/some/ay-z3shim-top3")
            self.assertEqual(env.get("AY_BIN"), sys.executable)
            self.assertEqual(env.get("AY_SHIM_ARGS"), "-q --z3-mode")
            for key, sub in (("AY_SHIM_EVENT_DIR", "events"), ("AY_SHIM_TRANSCRIPT_DIR", "transcripts")):
                self.assertEqual(Path(env.get(key, "/missing")).resolve(), (out / sub).resolve(), key)
            self.assertNotIn("SHIM_SOLVER", env, "an ay run must never be redirected to z3")

    def test_run_one_needs_the_exact_rustc_driver(self):
        with tempfile.TemporaryDirectory(prefix="verus-suite-harness-") as tmp:
            tmp = Path(tmp)
            root, lib, dump = self.fake_stage(tmp)
            (lib / suite_common.RUSTC_DRIVER).rename(lib / "librustc_driver-0123456789abcdef.dylib")
            p = run([HERE / "run_one.sh", "lbl", "z3", tmp / "one", "fakebin", "t1"],
                    env=clean_env(VERUS_SUITE_OUT_ROOT=str(root), VERUS_SUITE_DYLD=str(lib)))
            self.assertEqual(p.returncode, 2, p.stderr)
            self.assertIn(suite_common.RUSTC_DRIVER, p.stderr)
            self.assertFalse(dump.exists(), "the test binary was launched without its library")


class PathsTest(unittest.TestCase):
    def test_verus_resolution_order(self):
        env = dict(os.environ)
        try:
            os.environ.pop("TRUST_VC_VERUS_PATH", None)
            os.environ.pop("VERUS_PATH", None)
            self.assertEqual(suite_common.resolve_verus(None), (REPO.parent / "verus").absolute())
            os.environ["VERUS_PATH"] = "/tmp/v-plain"
            self.assertEqual(suite_common.resolve_verus(None), Path("/tmp/v-plain"))
            os.environ["TRUST_VC_VERUS_PATH"] = "/tmp/v-trust-vc"
            self.assertEqual(suite_common.resolve_verus(None), Path("/tmp/v-trust-vc"))
            self.assertEqual(suite_common.resolve_verus("/tmp/v-flag"), Path("/tmp/v-flag"))
        finally:
            os.environ.clear()
            os.environ.update(env)

    def test_resolve_dyld_needs_the_exact_driver(self):
        with tempfile.TemporaryDirectory(prefix="verus-suite-dyld-") as tmp:
            lib = Path(tmp)
            (lib / "librustc_driver-0123456789abcdef.dylib").write_bytes(b"")
            with self.assertRaises(SystemExit) as cm:
                suite_common.resolve_dyld(lib)
            self.assertIn(suite_common.RUSTC_DRIVER, str(cm.exception))
            (lib / suite_common.RUSTC_DRIVER).write_bytes(b"")
            self.assertEqual(suite_common.resolve_dyld(lib), lib.absolute())

    def test_display_path_hides_the_home_directory(self):
        home = str(Path.home())
        self.assertEqual(suite_common.display_path(home + "/verus/source/z3"), "~/verus/source/z3")
        self.assertEqual(suite_common.display_path("/opt/z3"), "/opt/z3")

    def test_out_root_is_gitignored(self):
        self.assertIn(".verus-suite/", (REPO / ".gitignore").read_text().splitlines())


def write_bins(run_dir, results):
    """A run_suite.py per-binary cache: results = {(binary, test): outcome}."""
    (run_dir / "bins").mkdir(parents=True)
    by_bin = {}
    for (b, t), o in results.items():
        by_bin.setdefault(b, {})[t] = {"outcome": o, "exec_time": 0.1, "message": "", "detail": "", "attempt": 1}
    for b, res in by_bin.items():
        (run_dir / "bins" / f"{b}.json").write_text(json.dumps(
            {"binary": b, "results": res, "discovery": {t: {"line": 7} for t in res}}))


def write_events(run_dir, key, procs):
    (run_dir / "events").mkdir(parents=True, exist_ok=True)
    (run_dir / "events" / f"{key}.jsonl").write_text("".join(json.dumps(p) + "\n" for p in procs))


def proc(answers, killed=None, rc=0, pending=0, unanswered=()):
    return {"test": "", "pid": 1, "start": 0, "rc": rc, "killed": killed, "answers": answers,
            "pending_at_exit": pending, "unanswered_prefix": list(unanswered), "errors": [],
            "stdin_bytes": 10, "stderr_tail": ""}


class ClassifyTest(unittest.TestCase):
    def test_synthetic_run_against_a_results_csv_reference(self):
        with tempfile.TemporaryDirectory(prefix="verus-suite-classify-") as tmp:
            runs = Path(tmp) / "runs"
            # the committed-reference shape: results.csv, no bins/
            (runs / "z3").mkdir(parents=True)
            with open(runs / "z3" / "results.csv", "w", newline="") as f:
                w = csv.DictWriter(f, fieldnames=["binary", "test_file", "test_name", "line", "outcome",
                                                  "exec_time_s", "message", "detail", "attempt"])
                w.writeheader()
                for t in ("same", "slow", "nosolver"):
                    w.writerow({"binary": "basic", "test_file": "x", "test_name": t, "line": 7, "outcome": "ok",
                                "exec_time_s": 0.1, "message": "", "detail": "", "attempt": 1})
            write_bins(runs / "z3-shim", {("basic", "same"): "ok", ("basic", "slow"): "ok",
                                          ("basic", "nosolver"): "ok"})
            write_events(runs / "z3-shim", "basic-same", [proc([["unsat", 0.0, "h1"]])])
            write_events(runs / "z3-shim", "basic-slow", [proc([["unsat", 0.0, "h2"]])])
            write_bins(runs / "ay", {("basic", "same"): "ok", ("basic", "slow"): "FAILED",
                                     ("basic", "nosolver"): "ok"})
            write_events(runs / "ay", "basic-same", [proc([["unsat", 0.2, "h1"]])])
            write_events(runs / "ay", "basic-slow", [proc([], killed="check-sat unanswered after 60 s", rc=-9,
                                                          pending=1, unanswered=["h2"])])
            out = Path(tmp) / "out"
            p = run([sys.executable, HERE / "classify.py", "--label", "ay", "--out-root", tmp, "--out-dir", out])
            self.assertEqual(p.returncode, 0, p.stderr)
            rows = read_csv(out / "classified.csv")
            self.assertEqual([(r["test_name"], r["class"], r["subclass"]) for r in rows],
                             [("slow", "INCOMPLETE", "no answer within the wall where z3 proved unsat")])
            ok = {r["test_name"]: r["kind"] for r in read_csv(out / "ok-breakdown.csv")}
            self.assertEqual(ok, {"same": "every answer identical to z3", "nosolver": "no solver process"})
            self.assertFalse((runs / "ay" / "classified.csv").exists())

    def test_missing_run_is_refused(self):
        with tempfile.TemporaryDirectory(prefix="verus-suite-classify-") as tmp:
            p = run([sys.executable, HERE / "classify.py", "--label", "ay", "--out-root", tmp])
            self.assertNotEqual(p.returncode, 0)
            self.assertIn("no run 'ay'", p.stderr)


class CommittedReferenceTest(unittest.TestCase):
    """evals/verus/upstream-suite/ holds the z3 4.12.5 reference; keep it self-consistent."""

    def test_z3_reference_counts(self):
        rows = read_csv(SUITE / "runs" / "z3" / "results.csv")
        outcomes = {}
        for r in rows:
            outcomes[r["outcome"]] = outcomes.get(r["outcome"], 0) + 1
        self.assertEqual(len(rows), 4213)
        self.assertEqual(outcomes, {"ok": 4114, "ignored": 80, "not-run": 19})

    def test_excluded_is_exactly_what_z3_did_not_pass(self):
        rows = read_csv(SUITE / "runs" / "z3" / "results.csv")
        excluded = read_csv(SUITE / "excluded-from-comparison.csv")
        self.assertEqual({(r["binary"], r["test_name"]) for r in rows if r["outcome"] != "ok"},
                         {(r["binary"], r["test_name"]) for r in excluded})
        self.assertTrue(all(r["reason"] for r in excluded))

    def test_denominator_matches_the_reference(self):
        rows = read_csv(SUITE / "denominator.csv")
        ref = {(r["binary"], r["test_name"]): r["outcome"]
               for r in read_csv(SUITE / "runs" / "z3" / "results.csv")}
        self.assertEqual({(r["binary"], r["test_name"]): r["run_outcome"] for r in rows}, ref)


@unittest.skipUnless(os.environ.get("VERUS_BASELINE_ROOT"),
                     "set VERUS_BASELINE_ROOT to the recorded 2026-09-23 run tree to check reproduction")
class RecordedRunReproductionTest(unittest.TestCase):
    """(e) the landed tools reproduce the recorded outputs byte for byte."""

    def setUp(self):
        self.root = Path(os.environ["VERUS_BASELINE_ROOT"]).expanduser().absolute()
        self._tmp = tempfile.TemporaryDirectory(prefix="verus-suite-repro-")
        self.tmp = Path(self._tmp.name)

    def tearDown(self):
        self._tmp.cleanup()

    def test_classify_reproduces_the_recorded_classification(self):
        label = "ay-0919b4e16"
        recorded = self.root / "runs" / label
        if not (recorded / "classified.csv").exists():
            self.skipTest(f"{recorded}/classified.csv is not there")
        p = run([sys.executable, HERE / "classify.py", "--label", label, "--out-root", self.root,
                 "--out-dir", self.tmp], timeout=600)
        self.assertEqual(p.returncode, 0, p.stderr)
        for name in ("classified.csv", "query-diff.csv", "ok-breakdown.csv", "classified.md"):
            with self.subTest(output=name):
                self.assertEqual((self.tmp / name).read_bytes(), (recorded / name).read_bytes())

    def test_denominator_reproduces_the_recorded_csv(self):
        if not (self.root / "denominator.csv").exists():
            self.skipTest(f"{self.root}/denominator.csv is not there")
        verus = suite_common.resolve_verus(None)
        if not (verus / "source" / "target.noindex" / "debug" / "deps").is_dir():
            self.skipTest(f"no built Verus checkout at {verus} (set TRUST_VC_VERUS_PATH)")
        try:
            suite_common.resolve_dyld(None)
        except SystemExit as e:
            self.skipTest(str(e))
        p = run([sys.executable, HERE / "denominator.py", "--run", "z3", "--out-root", self.root,
                 "--out-dir", self.tmp, "--verus", verus], timeout=600)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertEqual((self.tmp / "denominator.csv").read_bytes(), (self.root / "denominator.csv").read_bytes())
        # the committed copy is the recorded csv, and the committed .md is this tool's output
        self.assertEqual((SUITE / "denominator.csv").read_bytes(), (self.root / "denominator.csv").read_bytes())
        self.assertEqual((self.tmp / "denominator.md").read_bytes(), (SUITE / "denominator.md").read_bytes())


if __name__ == "__main__":
    unittest.main()
