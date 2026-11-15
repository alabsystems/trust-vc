#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Reconcile the static case count of rust_verify_test/tests/*.rs with the tests the
prebuilt binaries actually contain (libtest --list), and with a finished run.

Static side: every `test_verify_one_file!`, `test_verify_one_file_with_options!`,
`test_verify_one_bv_file!` and `test_verify_one_bv_file_with_options!` invocation,
parsed the same way scripts/corpus_coverage.py does (macro start, matching brace,
`#[test] <attrs> name`). Runtime side: `<binary> --format json --list`, which names
every #[test] and its source line; listing runs no test and writes nothing.

Usage:
  denominator.py [--run z3] [--verus DIR] [--out-root DIR] [--out-dir DIR]
      -> <out-dir>/denominator.md, <out-dir>/denominator.csv
  denominator.py --results evals/verus/upstream-suite/runs/z3/results.csv \\
      --out-dir evals/verus/upstream-suite          # regenerate the committed copy

The run's outcomes come from --results, else <out-root>/runs/<run>/results.csv.
<out-dir> defaults to <out-root>. The Verus checkout is found as run_suite.py finds
it, and so is the rustc 1.95.0 library directory the binaries need (--dyld).
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import re
import subprocess
from pathlib import Path

import suite_common

# set from the arguments in main()
VERUS = Path()
TESTS = Path()
DEPS = Path()
DYLD = Path()

MACRO_START = re.compile(r"\b(test_verify_one_(?:bv_)?file(?:_with_options)?)!\s*\{")
TEST_NAME = re.compile(r"#\[test\]\s*((?:#\[[^\]]*\]\s*)*)([A-Za-z_][A-Za-z0-9_]*)")
MACRO_RULES = re.compile(r"\bmacro_rules!\s*[A-Za-z_][A-Za-z0-9_]*\s*\{")


def matching_brace(text, open_idx):
    depth = 0
    i = open_idx
    n = len(text)
    while i < n:
        c = text[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                i += 1
        i += 1
    return -1


def static_cases(path):
    text = path.read_text(encoding="utf-8")
    rules = []
    for m in MACRO_RULES.finditer(text):
        close = matching_brace(text, m.end() - 1)
        rules.append((m.start(), close))
    out = []
    for m in MACRO_START.finditer(text):
        line_start = text.rfind("\n", 0, m.start()) + 1
        commented = text[line_start:m.start()].lstrip().startswith("//")
        in_rules = any(a <= m.start() <= b for a, b in rules)
        open_idx = m.end() - 1
        close_idx = matching_brace(text, open_idx)
        block = text[open_idx + 1:close_idx] if close_idx >= 0 else ""
        nm = TEST_NAME.search(block)
        name = nm.group(2) if nm else None
        ignored = bool(nm) and ("#[ignore" in block[:nm.start()] or "ignore" in nm.group(1))
        out.append({
            "file": path.name, "macro": m.group(1), "line": text.count("\n", 0, m.start()) + 1,
            "name": name, "ignored": ignored, "commented": commented, "in_macro_rules": in_rules,
        })
    return out


def runtime_tests():
    env = dict(os.environ, DYLD_LIBRARY_PATH=str(DYLD), RUSTC_BOOTSTRAP="1")
    res = {}
    for p in sorted(DEPS.iterdir()):
        m = re.fullmatch(r"(.+)-([0-9a-f]{16})", p.name)
        if not m or not p.is_file() or "." in p.name or not (TESTS / f"{m.group(1)}.rs").exists():
            continue
        r = subprocess.run([str(p), "-Z", "unstable-options", "--format", "json", "--list"],
                           env=env, capture_output=True, text=True, timeout=120)
        tests = []
        for line in r.stdout.splitlines():
            try:
                e = json.loads(line)
            except json.JSONDecodeError:
                continue
            if e.get("event") == "discovered":
                tests.append({"name": e["name"], "ignore": e.get("ignore", False),
                              "line": e.get("start_line"), "source_path": e.get("source_path", "")})
        res[m.group(1)] = tests
    return res


def verus_rev(verus):
    r = subprocess.run(["git", "--no-optional-locks", "-C", str(verus), "rev-parse", "HEAD"],
                       capture_output=True, text=True)
    return r.stdout.strip()[:8] if r.returncode == 0 and r.stdout.strip() else "an unknown revision"


def main():
    global VERUS, TESTS, DEPS, DYLD
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--run", default="z3", help="run label whose results.csv to reconcile")
    ap.add_argument("--results", type=Path, default=None,
                    help="a results.csv to reconcile instead of <out-root>/runs/<run>/results.csv")
    ap.add_argument("--verus", "--verus-path", dest="verus", default=None,
                    help="Verus checkout, read only (default: TRUST_VC_VERUS_PATH, VERUS_PATH, ../verus)")
    ap.add_argument("--dyld", default=None, help=f"directory holding {suite_common.RUSTC_DRIVER}")
    ap.add_argument("--out-root", type=Path, default=None,
                    help="default: VERUS_SUITE_OUT_ROOT, else .verus-suite/ at the repo root")
    ap.add_argument("--out-dir", type=Path, default=None, help="where the outputs go (default: <out-root>)")
    args = ap.parse_args()
    out_root = args.out_root.expanduser().absolute() if args.out_root else suite_common.default_out_root()
    out_dir = args.out_dir.expanduser().absolute() if args.out_dir else out_root
    VERUS = suite_common.require_verus(suite_common.resolve_verus(args.verus))
    TESTS = VERUS / "source/rust_verify_test/tests"
    DEPS = VERUS / "source/target.noindex/debug/deps"
    DYLD = suite_common.resolve_dyld(args.dyld)

    static = {}
    for f in sorted(TESTS.glob("*.rs")):
        static[f.stem] = static_cases(f)
    runtime = runtime_tests()

    run_rows = {}
    rc = args.results if args.results else out_root / "runs" / args.run / "results.csv"
    run_name = args.run if not args.results else args.results.parent.name
    if rc.exists():
        with open(rc) as fh:
            for r in csv.DictReader(fh):
                run_rows[(r["binary"], r["test_name"])] = r["outcome"]

    rows = []
    agg = dict(tvof_all=0, tvof_named=0, tvof_named_ignored=0, tvof_unnamed=0, tvof_in_rules=0,
               tvof_commented=0, bv_all=0, bv_named=0, bv_ignored=0,
               rt_total=0, rt_ignored=0, rt_from_tvof=0, rt_from_bv=0, rt_other=0,
               static_missing_at_runtime=0)
    other_by_file = {}
    missing = []
    for name in sorted(set(static) | set(runtime)):
        cases = static.get(name, [])
        tests = runtime.get(name, [])
        live = [c for c in cases if c["name"] and not c["commented"] and not c["in_macro_rules"]]
        tv = [c for c in cases if not c["macro"].startswith("test_verify_one_bv")]
        bv = [c for c in cases if c["macro"].startswith("test_verify_one_bv")]
        agg["tvof_all"] += len(tv)
        agg["tvof_named"] += sum(1 for c in tv if c in live and not c["ignored"])
        agg["tvof_named_ignored"] += sum(1 for c in tv if c in live and c["ignored"])
        agg["tvof_unnamed"] += sum(1 for c in tv if not c["name"])
        agg["tvof_in_rules"] += sum(1 for c in tv if c["in_macro_rules"])
        agg["tvof_commented"] += sum(1 for c in tv if c["commented"])
        agg["bv_all"] += len(bv)
        agg["bv_named"] += sum(1 for c in bv if c in live and not c["ignored"])
        agg["bv_ignored"] += sum(1 for c in bv if c in live and c["ignored"])
        live_names = {c["name"]: c for c in live}
        rt_names = {t["name"].split("::")[-1] for t in tests}
        for c in live:
            if c["name"] not in rt_names:
                missing.append((name, c))
        agg["static_missing_at_runtime"] += sum(1 for c in live if c["name"] not in rt_names)
        n_tv = n_bv = n_other = 0
        others = []
        for t in tests:
            short = t["name"].split("::")[-1]
            c = live_names.get(short)
            src = "other"
            if c is not None:
                src = "bv" if c["macro"].startswith("test_verify_one_bv") else "tvof"
            if src == "tvof":
                n_tv += 1
            elif src == "bv":
                n_bv += 1
            else:
                n_other += 1
                others.append(t)
            agg["rt_total"] += 1
            agg["rt_ignored"] += 1 if t["ignore"] else 0
            rows.append({"binary": name, "test_name": t["name"], "line": t["line"], "ignore": t["ignore"],
                         "static_source": src, "run_outcome": run_rows.get((name, t["name"]), "")})
        agg["rt_from_tvof"] += n_tv
        agg["rt_from_bv"] += n_bv
        agg["rt_other"] += n_other
        if others:
            other_by_file[name] = others

    out_dir.mkdir(parents=True, exist_ok=True)
    with open(out_dir / "denominator.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["binary", "test_name", "line", "ignore", "static_source", "run_outcome"])
        w.writeheader()
        w.writerows(rows)

    L = []
    L.append("# Denominator: static cases vs. tests in the prebuilt binaries\n")
    L.append(f"Static source: `<verus>/source/rust_verify_test/tests` at Verus {verus_rev(VERUS)}. "
             f"Runtime: `--list` of the prebuilt binaries in `<verus>/source/target.noindex/debug/deps`.\n")
    ex = len(other_by_file.get("examples", []))
    cg = len(other_by_file.get("cargo", []))
    plain = len(other_by_file.get("harness", [])) + len(other_by_file.get("summer_school", []))
    rules_gen = agg["rt_other"] - ex - cg - plain
    L.append("## Summary\n")
    L.append(f"- The binaries contain **{agg['rt_total']}** #[test] functions, and {agg['rt_ignored']} of them are `#[ignore]`.")
    L.append(f"- The static figure of {agg['tvof_named'] + agg['bv_named']:,} is {agg['tvof_named']} non-ignored named `test_verify_one_file` cases plus {agg['bv_named']} `test_verify_one_bv_file` cases.")
    L.append(f"- {agg['static_missing_at_runtime']} of those {agg['tvof_named']} cases are `#[cfg(target_pointer_width = \"32\")]` in layout.rs and are not compiled on this 64-bit host. The binaries therefore hold {agg['tvof_named'] - agg['static_missing_at_runtime']} + {agg['bv_named']} = {agg['tvof_named'] - agg['static_missing_at_runtime'] + agg['bv_named']} of them.")
    L.append(f"- Each bv test verifies its case twice: once with bit-vector simplification and once with `no-bv-simplify`.")
    L.append(f"- The static count leaves out these runtime tests:")
    L.append(f"  - {agg['tvof_named_ignored']} ignored named cases;")
    L.append(f"  - {rules_gen} tests that local `macro_rules!` generate from the {agg['tvof_unnamed']} unnamed templates;")
    L.append(f"  - {ex} `examples_in_dir!` tests, one per example file;")
    L.append(f"  - {cg} `cargo.rs` tests;")
    L.append(f"  - {plain} plain `#[test] fn`s in harness.rs and summer_school.rs.")
    L.append(f"- Check: {agg['tvof_named'] - agg['static_missing_at_runtime']} + {agg['bv_named']} + {agg['tvof_named_ignored']} + {rules_gen} + {ex} + {cg} + {plain} = {agg['tvof_named'] - agg['static_missing_at_runtime'] + agg['bv_named'] + agg['tvof_named_ignored'] + rules_gen + ex + cg + plain}.")
    L.append("")
    L.append("## Static count\n")
    L.append("| item | count |")
    L.append("|---|---|")
    L.append(f"| `test_verify_one_file[_with_options]!` invocations (all) | {agg['tvof_all']} |")
    L.append(f"| of those: named `#[test]`, not ignored | {agg['tvof_named']} |")
    L.append(f"| of those: named `#[test]`, `#[ignore]` (incl. cfg_attr ignore) | {agg['tvof_named_ignored']} |")
    L.append(f"| of those: no `#[test] name` in the block (templates inside `macro_rules!`, name is `$name`) | {agg['tvof_unnamed']} |")
    L.append(f"| of those: inside a `macro_rules!` body | {agg['tvof_in_rules']} |")
    L.append(f"| of those: commented out | {agg['tvof_commented']} |")
    L.append(f"| `test_verify_one_bv_file[_with_options]!` invocations | {agg['bv_all']} (named, not ignored: {agg['bv_named']}; ignored: {agg['bv_ignored']}) |")
    L.append("")
    L.append("## Runtime count (libtest `--list`, 129 test binaries incl. cargo)\n")
    L.append("| item | count |")
    L.append("|---|---|")
    L.append(f"| #[test] functions | {agg['rt_total']} |")
    L.append(f"| of which `#[ignore]` | {agg['rt_ignored']} |")
    L.append(f"| matched to a named `test_verify_one_file` case | {agg['rt_from_tvof']} |")
    L.append(f"| matched to a named `test_verify_one_bv_file` case (one test runs the case twice: bv simplify on, then off) | {agg['rt_from_bv']} |")
    L.append(f"| not from a named static case (see below) | {agg['rt_other']} |")
    L.append(f"| named static cases with no runtime test | {agg['static_missing_at_runtime']} |")
    L.append("")
    WHY = {
        "examples": "`examples_in_dir!`: one test per .rs file under <verus>/examples (8 dirs)",
        "cargo": "`cargo_examples!` (17 dirs under tests/cargo-tests) + 2 plain #[test] fns; they run `cargo`",
        "harness": "plain #[test] fns that call verify_one_file directly",
        "summer_school": "plain #[test] fns that call verify_files (multi-file)",
    }
    L.append("## Runtime tests that are not a named static case, by file\n")
    L.append("| file | tests | ignored | how they are generated | examples |")
    L.append("|---|---|---|---|---|")
    for name, ts in sorted(other_by_file.items(), key=lambda kv: -len(kv[1])):
        ex = ", ".join(t["name"] for t in ts[:3]) + (" ..." if len(ts) > 3 else "")
        why = WHY.get(name, "a local `macro_rules!` that expands to `test_verify_one_file!` (one of the 20 unnamed templates)")
        L.append(f"| {name}.rs | {len(ts)} | {sum(1 for t in ts if t['ignore'])} | {why} | {ex} |")
    L.append("")
    if run_rows:
        from collections import Counter
        c = Counter((r["static_source"], r["run_outcome"]) for r in rows)
        L.append(f"## Reconciliation with run `{run_name}`\n")
        L.append("| static source | outcome | tests |")
        L.append("|---|---|---|")
        for (s, o), k in sorted(c.items()):
            L.append(f"| {s} | {o} | {k} |")
        L.append("")
    if missing:
        L.append("## Named static cases with no runtime test\n")
        for name, c in missing:
            L.append(f"- {name}.rs:{c['line']} `{c['name']}` ({c['macro']})")
        L.append("")
    (out_dir / "denominator.md").write_text("\n".join(L))
    print("\n".join(L))
    print(json.dumps(agg))


if __name__ == "__main__":
    main()
