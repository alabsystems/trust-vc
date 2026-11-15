#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Re-run selected tests of a classified run, each alone, with ay behind the measurement shim.

  rerun_tests.py --label ay-<sha> --out <dir> --wall 330 --jobs 4 \
      (--subclass "<text>" [--sample N --seed S] | --tests bin::test,...) [--out-root DIR]

Uses run_one.sh in the idle stage of the z3-shim run (--stage; so nothing is written
into the stage of the run being studied), with AY_SHIM_QUERY_WALL_S=<wall>. The ay
binary is --ay-bin, else AY_BIN, and one of them is REQUIRED: the AY_BIN the classified
run recorded in its run.json is never used, because a recorded path can hold a
different build by now. Writes <out>/<binary>-<test>/{libtest.jsonl, events/,
transcripts/} and <out>/summary.csv: per test, the outcome and, for the query the
classifier flagged (by prefix hash, else by position), ay's answer and time in the
re-run. Other shim options (AY_SHIM_DROP_STDERR, AY_SHIM_RLIMIT_MONOTONE,
AY_SHIM_QUERY_CPU_S, ...) pass through from this environment. When run_one.sh refuses
(no stage, no library, ...) the driver stops with its message and writes no summary.
"""
import argparse
import csv
import json
import os
import random
import re
import subprocess
from pathlib import Path

import suite_common


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--label", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--wall", type=int, default=330)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--subclass", default="")
    ap.add_argument("--tests", default="")
    ap.add_argument("--sample", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--transcripts", action="store_true")
    ap.add_argument("--test-limit", type=int, default=900, help="kill a re-run test after this many seconds")
    ap.add_argument("--stage", default="z3-shim", help="label whose stage the re-runs use (default: %(default)s)")
    ap.add_argument("--ay-bin", default=os.environ.get("AY_BIN", ""),
                    help="default: AY_BIN; one of them is required (the run's recorded AY_BIN is never used)")
    ap.add_argument("--out-root", type=Path, default=None,
                    help="default: VERUS_SUITE_OUT_ROOT, else .verus-suite/ at the repo root")
    a = ap.parse_args()
    ay_bin = suite_common.require_ay_bin(a.ay_bin, "--ay-bin or AY_BIN")
    root = a.out_root.expanduser().absolute() if a.out_root else suite_common.default_out_root()
    run_json = json.loads((root / "runs" / a.label / "run.json").read_text())
    env0 = run_json["invocations"][0]["env"]
    rows = list(csv.DictReader(open(root / "runs" / a.label / "classified.csv")))
    if a.tests:
        want = {tuple(t.split("::")) for t in a.tests.split(",")}
        rows = [r for r in rows if (r["binary"], r["test_name"]) in want]
    else:
        rows = [r for r in rows if r["subclass"] == a.subclass]
    if a.sample and len(rows) > a.sample:
        rows = random.Random(a.seed).sample(rows, a.sample)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)

    def one(r):
        d = out / f"{r['binary']}-{r['test_name']}"
        env = suite_common.run_one_env(root, AY_BIN=ay_bin, AY_SHIM_ARGS=env0.get("AY_SHIM_ARGS", "-q --z3-mode"),
                                       AY_SHIM_QUERY_WALL_S=str(a.wall))
        killed = suite_common.run_one([a.stage, "ay", d, r["binary"], r["test_name"]], env, a.test_limit)
        if not a.transcripts:
            subprocess.run(["rm", "-rf", str(d / "transcripts")])
        outcome = "killed at --test-limit" if killed else "no libtest result"
        for line in open(d / "libtest.jsonl") if (d / "libtest.jsonl").exists() else []:
            try:
                e = json.loads(line)
            except json.JSONDecodeError:
                continue
            if e.get("type") == "test" and e.get("event") in ("ok", "failed"):
                outcome = e["event"]
        procs = [json.loads(l) for f in (d / "events").glob("*.jsonl") for l in open(f) if l.strip()]
        hit = None
        for p in procs:
            for i, ans in enumerate(p["answers"]):
                if ans[2] == r["query_hash"]:
                    hit = (ans, p)
            if hit is None and r["query_hash"] in p.get("unanswered_prefix", []):
                hit = (None, p)
        rec = {"binary": r["binary"], "test_name": r["test_name"], "run_subclass": r["subclass"],
               "rerun_outcome": outcome, "flagged_query_seen": hit is not None,
               "rerun_answer": (hit[0][0] + (" " + hit[0][3] if len(hit[0]) > 3 else "")) if hit and hit[0] else
               ("no answer: " + str(hit[1].get("killed")) if hit else ""),
               "rerun_secs": hit[0][1] if hit and hit[0] else "",
               "procs": len(procs),
               "killed": sum(1 for p in procs if p.get("killed")),
               "errors": "; ".join(sorted({x[:80] for p in procs for x in
                                          re.findall(r'\(error "([^"]*)', p.get("stderr_tail", ""))}))}
        print(rec, flush=True)
        return rec

    recs = suite_common.pool_map(one, rows, a.jobs)
    with open(out / "summary.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(recs[0].keys()) if recs else ["binary"])
        w.writeheader()
        w.writerows(recs)


if __name__ == "__main__":
    main()
