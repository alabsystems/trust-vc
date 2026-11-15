#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Run a list of tests, one test per libtest process, through run_one.sh with a
given shim, and record each outcome.

  run_tests_with_shim.py --tests-file F --out DIR [--shim PATH] [--jobs 4] [--stage z3-shim]

F holds binary::test entries separated by commas or newlines. --shim defaults to the
measurement shim next to this script; its options (AY_BIN, which is required, and
AY_SHIM_QUERY_CPU_S, AY_SHIM_DROP_STDERR, AY_SHIM_RLIMIT_MONOTONE, ...) come from
this environment. Writes DIR/<binary>-<test>/{libtest.jsonl, events/} and
DIR/summary.csv. Resumable. When run_one.sh refuses (no stage, no library, ...) the
driver stops with its message and writes no summary.
"""
import argparse
import csv
import json
import os
import re
import subprocess
from collections import Counter
from pathlib import Path

import suite_common


def outcome(d):
    f = d / 'libtest.jsonl'
    res = None
    if f.exists():
        for l in open(f):
            try:
                e = json.loads(l)
            except json.JSONDecodeError:
                continue
            if e.get('type') == 'test' and e.get('event') in ('ok', 'failed'):
                res = (e['event'], e.get('stdout', ''))
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--shim', default=str(suite_common.SHIM), help='VERUS_Z3_PATH for the tests')
    ap.add_argument('--tests-file', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--wall', default='60')
    ap.add_argument('--stage', default='z3-shim', help='label whose stage the tests run in')
    ap.add_argument('--out-root', type=Path, default=None,
                    help='default: VERUS_SUITE_OUT_ROOT, else .verus-suite/ at the repo root')
    a = ap.parse_args()
    suite_common.require_ay_bin(os.environ.get('AY_BIN'), 'environment')
    root = a.out_root.expanduser().absolute() if a.out_root else suite_common.default_out_root()
    shim = Path(a.shim).expanduser().absolute()
    tests = [t for t in re.split(r'[,\n]', open(a.tests_file).read()) if t.strip()]
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)

    def one(t):
        b, n = t.strip().split('::')
        d = out / f'{b}-{n}'
        if not outcome(d):
            subprocess.run(['rm', '-rf', str(d)])
            env = suite_common.run_one_env(root, SHIM=str(shim), AY_SHIM_QUERY_WALL_S=a.wall)
            suite_common.run_one([a.stage, 'ay', d, b, n], env)
            subprocess.run(['rm', '-rf', str(d / 'transcripts')])
        o = outcome(d)
        msg = ''
        if o and o[0] == 'failed':
            m = re.search(r'(panicked at [^\n]*\n[^\n]*)', o[1])
            msg = m.group(1)[:300] if m else o[1][-300:]
        return {'binary': b, 'test_name': n, 'outcome': o[0] if o else 'none', 'message': msg}

    recs = suite_common.pool_map(one, tests, a.jobs)
    with open(out / 'summary.csv', 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=['binary', 'test_name', 'outcome', 'message'])
        w.writeheader()
        w.writerows(recs)
    print(Counter(r['outcome'] for r in recs))


if __name__ == '__main__':
    main()
