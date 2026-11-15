#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Confirm or refute each SOUNDNESS candidate of a classified run.

  confirm_soundness.py --label ay-<sha> [--wall 300] [--only <binary>-<test>,...]
      [--ay-bin <ay>] [--stage <label>] [--verus DIR] [--out-root DIR]

For every row of <out-root>/runs/<label>/classified.csv with class SOUNDNESS:
  1. re-runs that one test with ay behind the measurement shim, with SMT
     transcripts on (run_one.sh, in the stage of --stage, default the label's own),
     into <out-root>/probes/<label>/<binary>-<test>/ay/;
  2. finds the query the classifier flagged (by its prefix hash; the shim hashes
     every byte AIR sent up to that (check-sat)) and cuts it out of the transcript
     as query.smt2 (the whole stream up to that check-sat);
  3. runs that file through
       z3 4.12.5 as Verus runs it (mbqi off, Verus's rlimit)       -> z3-verus
       z3 4.12.5 with smt.mbqi true, rlimit 0, -T:<wall>           -> z3-mbqi
       ay (z3 mode, as the suite ran it)                           -> ay
     and reads the answer to the LAST check-sat of each;
  4. verdict: CONFIRMED when z3-mbqi answers sat (the query has a model, so ay's
     unsat is wrong); REFUTED when z3-mbqi answers unsat (the query is valid; ay
     proved something z3 cannot prove with Verus's settings, which is not a
     soundness bug); UNDETERMINED otherwise.
Writes <out-root>/soundness-confirmations.json (keyed by query hash and by
<binary>-<test>) and <out-root>/probes/<label>/soundness.md. z3 is Verus's own,
<verus>/source/target-verus/debug/z3. AY_BIN (or --ay-bin) is required.
"""
import argparse
import csv
import glob
import hashlib
import json
import os
import re
import signal
import subprocess
import time
from pathlib import Path

import suite_common


def run(cmd, path, wall):
    t0 = time.time()
    with open(path, "rb") as f:
        p = subprocess.Popen(cmd, stdin=f, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        try:
            out, err = p.communicate(timeout=wall)
            hit = False
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            out, err = p.communicate()
            hit = True
    lines = [l.strip() for l in out.decode(errors="replace").splitlines()]
    answers = [l for l in lines if l in ("sat", "unsat", "unknown")]
    reasons = [l for l in lines if l.startswith("(:reason-unknown")]
    errors = [l[:200] for l in lines if l.startswith("(error")]
    return {"last": answers[-1] if answers else None, "answers": answers, "reasons": reasons[-2:],
            "errors": errors[:5], "wall_s": round(time.time() - t0, 2), "rc": p.returncode,
            "wall_hit": hit, "stderr_tail": err.decode(errors="replace")[-300:].strip()}


def cut(transcript, idx, dst):
    h = hashlib.sha256()
    n = -1
    out = []
    with open(transcript, "rb") as f:
        for line in f:
            out.append(line)
            h.update(line)
            if line.strip() == b"(check-sat)":
                n += 1
                if n == idx:
                    break
    if n != idx:
        return None
    with open(dst, "wb") as f:
        f.writelines(out)
        f.write(b'(echo "<<DONE>>")\n(get-info :reason-unknown)\n(echo "<<DONE>>")\n')
    return h.hexdigest()[:20]


def mbqi_variant(src, dst):
    s = Path(src).read_text()
    s = s.replace("(set-option :smt.mbqi false)", "(set-option :smt.mbqi true)")
    s = re.sub(r"\(set-option :rlimit \d+\)", "(set-option :rlimit 0)", s)
    Path(dst).write_text(s)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--label", required=True)
    ap.add_argument("--wall", type=float, default=300)
    ap.add_argument("--only", default="")
    ap.add_argument("--ay-bin", default=os.environ.get("AY_BIN", ""), help="default: AY_BIN (required)")
    ap.add_argument("--ay-args", default=os.environ.get("AY_SHIM_ARGS", "-q --z3-mode"))
    ap.add_argument("--stage", default=None, help="label whose stage the re-run uses (default: --label)")
    ap.add_argument("--verus", "--verus-path", dest="verus", default=None,
                    help="Verus checkout, for its z3 (default: TRUST_VC_VERUS_PATH, VERUS_PATH, ../verus)")
    ap.add_argument("--out-root", type=Path, default=None,
                    help="default: VERUS_SUITE_OUT_ROOT, else .verus-suite/ at the repo root")
    a = ap.parse_args()
    a.ay_bin = suite_common.require_ay_bin(a.ay_bin, "--ay-bin / AY_BIN")
    root = a.out_root.expanduser().absolute() if a.out_root else suite_common.default_out_root()
    z3 = str(suite_common.require_verus(suite_common.resolve_verus(a.verus)) / "source/target-verus/debug/z3")
    stage = a.stage or a.label
    rows = [r for r in csv.DictReader(open(root / "runs" / a.label / "classified.csv")) if r["class"] == "SOUNDNESS"]
    only = {x for x in a.only.split(",") if x}
    conf_path = root / "soundness-confirmations.json"
    conf = json.loads(conf_path.read_text()) if conf_path.exists() else {}
    report = []
    for r in rows:
        tk = f"{r['binary']}-{r['test_name']}"
        if only and tk not in only:
            continue
        out = root / "probes" / a.label / tk
        (out / "ay").mkdir(parents=True, exist_ok=True)
        env = suite_common.run_one_env(root, AY_BIN=a.ay_bin, AY_SHIM_ARGS=a.ay_args,
                                       AY_SHIM_QUERY_WALL_S=str(int(a.wall)))
        try:
            suite_common.run_one([stage, "ay", out / "ay", r["binary"], r["test_name"]], env)
        except suite_common.RunOneRefused as e:
            raise SystemExit(f"confirm_soundness.py: stopped at {tk}, nothing recorded for it: {e}")
        want = r["query_hash"]
        idx = int(r["query_index"]) if r["query_index"] else None
        found = None
        for evf in glob.glob(str(out / "ay/events/*.jsonl")):
            for line in open(evf):
                e = json.loads(line)
                for i, ans in enumerate(e["answers"]):
                    if ans[2] == want:
                        found = (e["pid"], i, ans)
        rec = {"test": tk, "query_hash": want, "query_index": idx, "run_answer": r["ay_answer"],
               "z3_answer_in_suite": r["z3_answer"]}
        if not found:
            rec["verdict"] = "UNDETERMINED"
            rec["why"] = "the re-run did not send the flagged query again (answers before it changed)"
        else:
            pid, i, ans = found
            tr = glob.glob(str(out / f"ay/transcripts/*/*-{pid}.in.smt2"))
            q = out / "query.smt2"
            h = cut(tr[0], i, q) if tr else None
            rec["rerun_ay_answer"] = ans[0]
            rec["transcript"] = suite_common.display_path(tr[0]) if tr else None
            rec["query_file"] = suite_common.display_path(q)
            rec["cut_hash"] = h
            qm = out / "query-mbqi.smt2"
            mbqi_variant(q, qm)
            rec["z3_verus"] = run([z3, "-smt2", "-in"], q, a.wall)
            rec["z3_mbqi"] = run([z3, "-smt2", "-in", f"-T:{int(a.wall)}"], qm, a.wall + 10)
            rec["ay"] = run([a.ay_bin] + a.ay_args.split() + ["-smt2", "-in"], q, a.wall)
            m = rec["z3_mbqi"]["last"]
            rec["verdict"] = {"sat": "CONFIRMED", "unsat": "REFUTED"}.get(m, "UNDETERMINED")
            rec["why"] = f"z3 with MBQI answered {m}"
        conf[want] = rec
        conf[tk] = rec
        report.append(rec)
        print(tk, rec["verdict"], rec.get("why"), flush=True)
        conf_path.write_text(json.dumps(conf, indent=1))
    lines = ["# SOUNDNESS candidates: confirmation runs\n",
             "| test | verdict | why | z3 as Verus runs it | z3 with MBQI | ay standalone |", "|---|---|---|---|---|---|"]
    for rec in report:
        f = lambda k: (rec.get(k) or {}).get("last")
        lines.append(f"| {rec['test']} | {rec['verdict']} | {rec.get('why')} | {f('z3_verus')} | {f('z3_mbqi')} | {f('ay')} |")
    (root / "probes" / a.label).mkdir(parents=True, exist_ok=True)
    (root / "probes" / a.label / "soundness.md").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
