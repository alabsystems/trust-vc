#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Load-noise check: re-run every test that <out-root>/runs/<label>/classified.csv marks
INCOMPLETE because ay gave no answer within the shim's wall, ONE TEST PER PROCESS,
with a CPU budget instead of a wall budget.

  rerun_timeouts.py --label ay-<sha> --out <dir> --jobs 9 [--cpu 60] [--out-root DIR]

Each test runs through run_one.sh (stage of the idle z3-shim run, --stage) with the
measurement shim in its CPU-budget mode: a check-sat is abandoned only after ay's
process tree used AY_SHIM_QUERY_CPU_S=<cpu> CPU seconds on it (or 900 s of wall
time), so machine load cannot turn a solvable query into a timeout. In the recorded
2026-09-23 suite run the limit was 60 s of wall time at load 10-51, i.e. at most 60
CPU seconds, so this budget is at least as generous. The ay binary is --ay-bin, else
AY_BIN, and one of them is REQUIRED (not with --summarize-only): the AY_BIN the
classified run recorded in its run.json is never used, because a recorded path can
hold a different build by now. Resumable: a test whose directory already has a final
libtest result is skipped. Writes <out>/<binary>-<test>/{libtest.jsonl, events/,
transcripts/} and <out>/summary.csv (rebuilt from all directories at the end). A test
killed at --test-limit leaves a `killed-at-test-limit` file in its directory, so the
summary tells that kill apart from a test that ended without a result. When run_one.sh
refuses (no stage, no library, ...) the driver stops with its message and writes no
summary. To repeat the recorded recheck exactly, also set AY_SHIM_DROP_STDERR=1 and
AY_SHIM_RLIMIT_MONOTONE=1 (README.md).
"""
import argparse
import csv
import json
import os
import subprocess
from pathlib import Path

import suite_common

KILLED_MARK = 'killed-at-test-limit'


def outcome_of(d):
    f = d / 'libtest.jsonl'
    if not f.exists():
        return None
    out = None
    for line in open(f):
        try:
            e = json.loads(line)
        except json.JSONDecodeError:
            continue
        if e.get('type') == 'test' and e.get('event') in ('ok', 'failed'):
            out = e['event']
    return out


def summarize(d, r):
    procs = [json.loads(l) for f in (d / 'events').glob('*.jsonl') for l in open(f) if l.strip()]
    kills = [p for p in procs if p.get('killed')]
    hit = None
    for p in procs:
        for a in p['answers']:
            if a[2] == r['query_hash']:
                hit = a
    return {'binary': r['binary'], 'test_name': r['test_name'], 'suite_subclass': r['subclass'],
            'rerun_outcome': outcome_of(d) or ('no result (killed at --test-limit)' if (d / KILLED_MARK).exists()
                                               else 'no result'),
            'flagged_query_answer': (hit[0] + (' ' + hit[3] if len(hit) > 3 else '')) if hit else '',
            'flagged_query_secs': hit[1] if hit else '',
            'solver_procs': len(procs), 'kills': len(kills),
            'kill_reason': '; '.join(sorted({str(p['killed']) for p in kills})),
            'kill_cpu_s': max((p.get('kill_cpu_s') or 0 for p in kills), default=''),
            'kill_wall_s': max((p.get('kill_pending_s') or 0 for p in kills), default=''),
            'kill_loadavg': max((p.get('kill_loadavg') or 0 for p in kills), default=''),
            'errors': '; '.join(sorted({e[:100] for p in procs for e in p.get('errors', [])}))}


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--label', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--jobs', type=int, default=6)
    ap.add_argument('--cpu', type=int, default=60)
    ap.add_argument('--test-limit', type=int, default=3600)
    ap.add_argument('--summarize-only', action='store_true')
    ap.add_argument('--stage', default='z3-shim', help='label whose stage the re-runs use (default: %(default)s)')
    ap.add_argument('--ay-bin', default=os.environ.get('AY_BIN', ''),
                    help="default: AY_BIN; one of them is required (the run's recorded AY_BIN is never used)")
    ap.add_argument('--out-root', type=Path, default=None,
                    help='default: VERUS_SUITE_OUT_ROOT, else .verus-suite/ at the repo root')
    a = ap.parse_args()
    ay_bin = None
    if not a.summarize_only:
        ay_bin = suite_common.require_ay_bin(a.ay_bin, '--ay-bin or AY_BIN')
    root = a.out_root.expanduser().absolute() if a.out_root else suite_common.default_out_root()
    rows = [r for r in csv.DictReader(open(root / 'runs' / a.label / 'classified.csv'))
            if r['class'] == 'INCOMPLETE' and r['subclass'].startswith('no answer within the wall')]
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    run_json = json.loads((root / 'runs' / a.label / 'run.json').read_text())
    env0 = run_json['invocations'][0]['env']

    def one(r):
        d = out / f"{r['binary']}-{r['test_name']}"
        if outcome_of(d):
            return
        subprocess.run(['rm', '-rf', str(d)])
        env = suite_common.run_one_env(root, AY_BIN=ay_bin, AY_SHIM_ARGS=env0.get('AY_SHIM_ARGS', '-q --z3-mode'),
                                       SHIM=str(suite_common.SHIM), AY_SHIM_QUERY_CPU_S=str(a.cpu),
                                       AY_SHIM_QUERY_WALL_MAX_S='900')
        if suite_common.run_one([a.stage, 'ay', d, r['binary'], r['test_name']], env, a.test_limit):
            d.mkdir(parents=True, exist_ok=True)
            (d / KILLED_MARK).write_text(f'{a.test_limit}\n')
        print(json.dumps(summarize(d, r)), flush=True)

    if not a.summarize_only:
        suite_common.pool_map(one, rows, a.jobs)
    recs = [summarize(out / f"{r['binary']}-{r['test_name']}", r) for r in rows
            if (out / f"{r['binary']}-{r['test_name']}").exists()]
    with open(out / 'summary.csv', 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(recs[0].keys()) if recs else ['binary'])
        w.writeheader()
        w.writerows(recs)


if __name__ == '__main__':
    main()
