#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Classify every test that is ok on z3 but not ok on another solver run.

  classify.py --label ay-<sha> [--z3 z3] [--z3-events z3-shim] [--out-root DIR] [--out-dir DIR]

Every input is read under <out-root> (default: VERUS_SUITE_OUT_ROOT, else .verus-suite/
at the repository root), where run_suite.py wrote it. Outputs go to --out-dir (default
<out-root>/runs/<label>/); nothing else is written.

Inputs
  runs/<z3>/results.csv            the reference outcomes (z3 4.12.5, no shim); like every
                                   label it is read from runs/<z3>/bins/*.json when that
                                   directory exists, so a run can be classified while it
                                   is still going
  runs/<label>/results.csv         the run under test
  runs/<label>/events/<key>.jsonl  shim event log of the run under test
  runs/<z3-events>/events/         shim event log of z3 on the same suite (same
                                   Verus flags), used to compare answers query by
                                   query: the shim hashes every byte AIR sent up to
                                   each (check-sat), so equal hashes mean the same
                                   query.
  runs/<label>/rechecks/*/events/  (optional) solo re-runs whose event logs recover an
                                   (error ...) line the suite run lost
  runs/<label>/split/, runs/<z3-events>/split/
                                   solo re-runs of the examples whose event keys collide
                                   (split_rerun.sh)
  soundness-confirmations.json     (optional) the per-candidate verdicts of
                                   confirm_soundness.py

Outputs
  <out-dir>/classified.csv         one row per test that is ok on z3 and not ok here
  <out-dir>/query-diff.csv         every query where the two solvers' answers differ
                                   (all tests, including tests that still pass)
  <out-dir>/ok-breakdown.csv       per test ok on both: did it use the solver, and were
                                   its answers identical to z3's
  <out-dir>/classified.md          counts per class, SOUNDNESS first

Classes (primary class = the first point where this solver's answers leave z3's)
  SOUNDNESS     this solver answered unsat where z3 found a counterexample, and the
                test expected verification errors; confirmed or refuted separately
                (column `confirmed`).
  SOLVER-ERROR  the solver crashed / panicked / printed (error ...).
  INCOMPLETE    unknown (rlimit / gave up) or killed at the shim wall where z3
                answered (unsat, or found a counterexample).
  PROTOCOL      output AIR cannot use: a reason-unknown AIR rejects, an
                unparseable model, unexpected lines.
  OTHER         anything else, with a subclass saying what.
"""
import argparse
import collections
import csv
import json
import re
from pathlib import Path

import suite_common

RUNS = suite_common.default_out_root() / "runs"  # set from --out-root in main()

CANCELED = {'(:reason-unknown "canceled")', '(:reason-unknown "unknown")'}


def load_results(label):
    """Per-test outcomes from the runner's cached per-binary results (bins/*.json),
    so a run can be classified while it is still going. A label with no bins/ (a
    committed reference keeps only results.csv) is read from results.csv."""
    rows = {}
    if not (RUNS / label / "bins").is_dir() and (RUNS / label / "results.csv").exists():
        with open(RUNS / label / "results.csv", newline="") as f:
            for r in csv.DictReader(f):
                rows[(r["binary"], r["test_name"])] = {
                    "binary": r["binary"], "test_name": r["test_name"], "line": r["line"],
                    "outcome": r["outcome"], "exec_time_s": r["exec_time_s"],
                    "message": r["message"], "detail": r["detail"]}
        return rows
    for p in sorted((RUNS / label / "bins").glob("*.json")):
        data = json.loads(p.read_text())
        disc = data.get("discovery", {})
        for t, r in data["results"].items():
            rows[(data["binary"], t)] = {
                "binary": data["binary"], "test_name": t, "line": disc.get(t, {}).get("line", ""),
                "outcome": r["outcome"], "exec_time_s": r.get("exec_time", ""),
                "message": r.get("message", ""), "detail": r.get("detail", "")}
    return rows


def load_events(label):
    d = RUNS / label / "events"
    ev = {}
    if not d.is_dir():
        return ev
    for p in d.glob("*.jsonl"):
        procs = []
        for line in p.read_text(errors="replace").splitlines():
            try:
                procs.append(json.loads(line))
            except json.JSONDecodeError:
                pass
        ev[p.stem] = procs
    return ev


def event_key(binary, test, keys):
    """The harness names a test's input dir <binary>-<fn name>; examples.rs uses
    example-<file stem>."""
    k = f"{binary}-{test.split('::')[-1]}"
    if k in keys:
        return k
    if binary == "examples":
        # test names are examples_<dir parts>_<stem>; pick the longest stem that matches
        best = None
        for key in keys:
            if key.startswith("example-"):
                stem = key[len("example-"):]
                if test.endswith("_" + stem.replace("-", "_")) or test == "examples_" + stem:
                    if best is None or len(key) > len(best):
                        best = key
        return best
    return None


def cat(ans):
    """Normalize one answer entry [answer, secs, hash, reason?] to a verdict class."""
    a = ans[0]
    reason = ans[3] if len(ans) > 3 else ""
    if a == "unsat":
        return "unsat"
    if a == "sat":
        return "sat"
    if a == "unknown":
        if reason in CANCELED:
            return "canceled"
        if reason.startswith('(:reason-unknown "(incomplete') or reason == \
                '(:reason-unknown "smt tactic failed to show goal to be sat/unsat (incomplete quantifiers)")':
            return "incomplete"
        if not reason:
            return "unknown-noreason"
        return "unknown-badreason"
    return "other:" + a


INVALID = {"sat", "incomplete"}  # AIR reads both as "not valid" and asks for a model


def proc_tail(p):
    """What happened after the last answer of a solver process."""
    if p.get("killed"):
        return "killed-wall" if "check-sat unanswered" in p["killed"] else "killed-eof"
    if p.get("pending_at_exit"):
        return "died-pending" if p.get("rc", 0) != 0 else "exit-pending"
    if p.get("rc", 0) != 0:
        return "died"
    return "ok"


def first_hash(p):
    if p["answers"]:
        return p["answers"][0][2]
    if p.get("unanswered_prefix"):
        return p["unanswered_prefix"][0]
    return None


def pair_processes(ay_procs, z3_procs):
    """Pair solver processes by the hash of their first query. Verus does not
    always emit a module's declarations in the same order (seen in state-machine
    tests), so a process whose first query has no exact match is paired with a
    leftover z3 process of the same test by size of the stream, and the pair is
    marked fuzzy: its answers are then compared by position, not by hash."""
    z3_by = collections.defaultdict(list)
    for p in z3_procs:
        z3_by[first_hash(p)].append(p)
    pairs = []
    left = []
    for p in sorted(ay_procs, key=lambda p: p.get("start", 0)):
        h = first_hash(p)
        lst = z3_by.get(h)
        if lst:
            pairs.append((p, lst.pop(0), False))
        else:
            left.append(p)
    unpaired_z3 = [p for lst in z3_by.values() for p in lst]
    for p in left:
        if unpaired_z3:
            q = min(unpaired_z3, key=lambda q: abs(q.get("stdin_bytes", 0) - p.get("stdin_bytes", 0)))
            unpaired_z3.remove(q)
            pairs.append((p, q, True))
        else:
            pairs.append((p, None, False))
    return pairs, unpaired_z3


def diff_pair(a, z, fuzzy=False):
    """Walk the two processes' answers in lockstep. Returns a dict describing the
    first divergence, or None if the answers are identical."""
    aa, za = a["answers"], z["answers"] if z else []
    n = min(len(aa), len(za))
    for i in range(n):
        if aa[i][2] != za[i][2] and not fuzzy:
            # the same answers so far but a different query: AIR sent something
            # different after an earlier answer (for a counterexample: the model
            # picked a different failing assertion)
            return {"kind": "stream", "index": i, "hash": aa[i][2], "z3": cat(za[i]), "ay": cat(aa[i]),
                    "prev": [cat(x) for x in aa[:i]]}
        ca, cz = cat(aa[i]), cat(za[i])
        if ca != cz:
            return {"kind": "answer", "index": i, "hash": aa[i][2], "z3": cz, "ay": ca,
                    "z3_reason": za[i][3] if len(za[i]) > 3 else "",
                    "ay_reason": aa[i][3] if len(aa[i]) > 3 else "",
                    "ay_secs": aa[i][1], "z3_secs": za[i][1]}
    if len(aa) < len(za):
        z = za[len(aa)]
        tail = proc_tail(a)
        return {"kind": "noanswer", "index": len(aa), "hash": z[2], "z3": cat(z), "ay": tail,
                "z3_secs": z[1]}
    if len(aa) > len(za):
        return {"kind": "extra", "index": len(za), "hash": aa[len(za)][2], "z3": proc_tail(z) if z else "none",
                "ay": cat(aa[len(za)])}
    if proc_tail(a) not in ("ok",) and (z is None or proc_tail(z) == "ok"):
        return {"kind": "tail", "index": len(aa), "hash": a.get("unanswered_prefix", [None])[0]
                if a.get("unanswered_prefix") else None, "z3": "ok", "ay": proc_tail(a)}
    return None


ERR_RE = re.compile(r'\(error "([^"]*)')


def solver_errors(p):
    """(error ...) lines the solver printed, on stdout (forwarded to AIR) or stderr."""
    out = [m.group(1) for e in p.get("errors", []) for m in [ERR_RE.search(e)] if m]
    out += ERR_RE.findall(p.get("stderr_tail", ""))
    # AIR asks (get-model) after an unknown and accepts "model is not available"
    # (air/src/smt_verify.rs:414); that reply is part of the protocol, not a failure
    return [e for e in out if "model is not available" not in e]


def norm_error(msg):
    msg = re.sub(r"\. Logics with a dedicated route:.*", "", msg)
    msg = re.sub(r"\d+", "N", msg)
    return msg[:110]


PRIORITY = {"SOUNDNESS": 0, "SOLVER-ERROR": 1, "PROTOCOL": 2, "INCOMPLETE": 3, "OTHER": 4}


def classify_proc(d, confirmations, test_key, recheck=()):
    """Class of one solver process that left z3's answers."""
    a = d["ay_proc"]
    errs = solver_errors(a)
    if "panicked" in a.get("stderr_tail", ""):
        m = re.search(r"panicked at ([^\n]*)\n([^\n]*)", a["stderr_tail"])
        return "SOLVER-ERROR", "panic" + (f": {m.group(2)[:90]}" if m else ""), {"stderr": a["stderr_tail"][-600:]}
    if d["kind"] == "answer" and d["ay"] == "unsat" and d["z3"] in INVALID:
        conf = confirmations.get(d["hash"]) or confirmations.get(test_key)
        if conf and conf.get("verdict") == "REFUTED":
            # z3 itself proves the query once MBQI is on: ay is right, and the test
            # expects a failure only because z3 instantiates by triggers alone
            return "OTHER", ("ay proved a valid query that z3 cannot prove with Verus's trigger-only settings "
                             "(SOUNDNESS candidate, refuted: z3 with MBQI also answers unsat)"), {"confirmation": conf}
        return "SOUNDNESS", f"unsat where z3 answered {d['z3']}" + (
            f" ({conf.get('verdict')})" if conf else " (not yet checked)"), {"confirmation": conf}
    if errs:
        return "SOLVER-ERROR", "(error) " + norm_error(errs[0]), {"errors": errs[:3], "rc": a.get("rc")}
    zp = d.get("z3_proc") or {}
    if (a.get("rc") not in (0, None) and zp.get("rc") in (0, None) and not a.get("killed")
            and not a.get("stderr_tail", "").strip() and d["ay"] in ("unknown-noreason", "died", "died-pending")):
        # before 19:59 on 2026-09-23 the shim could log a process before its stderr
        # reader had drained, so an (error ...) line can be missing; a re-run of these
        # tests with the fixed shim (rerun_tests.py into runs/<label>/rechecks/<test>/)
        # supplies the text
        rec = [e for p in recheck for e in solver_errors(p)]
        if rec:
            return "SOLVER-ERROR", "(error) " + norm_error(rec[0]), \
                {"errors": rec[:3], "rc": a.get("rc"), "error_text_from": "re-run"}
        return "SOLVER-ERROR", f"solver exited rc={a.get('rc')} without an error line captured", \
            {"stderr": a.get("stderr_tail", "")[-600:], "rc": a.get("rc")}
    z, y = d["z3"], d["ay"]
    if d["kind"] == "answer":
        if y == "unsat" and z == "canceled":
            return "OTHER", "ay proved a query z3 ran out of rlimit on", {}
        if y in ("unknown-badreason", "unknown-noreason"):
            return "PROTOCOL", "reason-unknown AIR does not accept: " + (d.get("ay_reason") or "none"), {}
        if z == "unsat" and y == "canceled":
            return "INCOMPLETE", "unknown (canceled: ay's own limit) where z3 proved unsat", {}
        if z == "unsat" and y == "incomplete":
            return "INCOMPLETE", "unknown (incomplete) where z3 proved unsat", {}
        if z == "unsat" and y == "sat":
            return "OTHER", "WRONG-SAT: sat where z3 proved unsat", {}
        if z in INVALID and y == "canceled":
            return "INCOMPLETE", "unknown (canceled: ay's own limit) where z3 found a counterexample", {}
        if z in INVALID and y in INVALID:
            return "OTHER", f"both not valid ({z} vs {y})", {}
        return "OTHER", f"answer {y} where z3 answered {z}", {}
    if d["kind"] == "noanswer":
        if y == "killed-wall":
            return "INCOMPLETE", ("no answer within the wall where z3 proved unsat" if z == "unsat" else
                                  "no answer within the wall where z3 found a counterexample" if z in INVALID else
                                  f"no answer within the wall where z3 answered {z}"), {}
        if y == "killed-eof":
            return "OTHER", "solver did not exit after stdin EOF", {}
        return "OTHER", f"no answer ({y}) where z3 answered {z}", {}
    if d["kind"] == "stream":
        nomodel = any("model is not available" in e for e in a.get("errors", []))
        gate = "MODEL-UNCONFIRMED" in a.get("stderr_tail", "")
        if nomodel:
            return "OTHER", ("same unknown answer as z3, but no model (ay: 'model is not available'"
                             + (", after its own gate rejected the candidate model" if gate else "")
                             + "), so Verus reports the error at the function instead of the failing assertion"), \
                {"stderr": a.get("stderr_tail", "")[-400:]}
        return "OTHER", "same answers, but ay's model points AIR at a different assertion", \
            {"stderr": a.get("stderr_tail", "")[-400:]}
    return "OTHER", f"process shape differs ({d['kind']}: ay {y}, z3 {z})", {}


def classify(row, ay_procs, z3_procs, confirmations, z3shim_outcome, recheck=()):
    """Returns (class, subclass, evidence dict, divergences)."""
    detail = row["detail"]
    test_key = f"{row['binary']}-{row['test_name']}"
    ev = {"ay_procs": len(ay_procs), "z3_procs": len(z3_procs)}
    divs = []
    if ay_procs:
        pairs, unpaired = pair_processes(ay_procs, z3_procs)
        for a, z, fz in pairs:
            d = diff_pair(a, z, fz)
            if d is not None:
                d["ay_proc"] = a
                d["z3_proc"] = z
                d["fuzzy"] = fz
                divs.append(d)
        ev["unpaired_ay"] = sum(1 for a, z, fz in pairs if z is None)
        ev["fuzzy_pairs"] = sum(1 for a, z, fz in pairs if fz)
        ev["unpaired_z3"] = len(unpaired)
    if z3shim_outcome not in ("ok", None):
        return "OTHER", "fails with z3 behind the same shim too (the test needs z3's own stderr)", ev, divs
    per = []
    for d in divs:
        c, sub, extra = classify_proc(d, confirmations, test_key, recheck)
        d["class"], d["subclass"] = c, sub
        per.append((PRIORITY[c], c, sub, extra, d))
    if per:
        per.sort(key=lambda x: x[0])
        _, c, sub, extra, d = per[0]
        ev.update(extra)
        ev["all_classes"] = sorted({f"{x[1]}: {x[2]}" for x in per})
        divs.remove(d)
        divs.insert(0, d)
        return c, sub, ev, divs
    # --- every answer matches z3; the failure is in what AIR did with the output
    if re.search(r"air/src/(parser|model|smt_verify)", detail) or "discovered_error" in detail:
        return "PROTOCOL", "answers match z3; AIR rejected the output: " + detail[:120], ev, divs
    if "unexpected" in detail.lower():
        return "PROTOCOL", "answers match z3; " + detail[:120], ev, divs
    if not ay_procs:
        return "OTHER", "no solver process logged for this test", ev, divs
    return "OTHER", "answers match z3; failure elsewhere", ev, divs


def main():
    global RUNS
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--label", required=True)
    ap.add_argument("--z3", default="z3")
    ap.add_argument("--z3-events", default="z3-shim")
    ap.add_argument("--out-root", type=Path, default=None,
                    help="where runs/ lives (default: VERUS_SUITE_OUT_ROOT, else .verus-suite/ at the repo root)")
    ap.add_argument("--out-dir", type=Path, default=None,
                    help="where the outputs go (default: <out-root>/runs/<label>)")
    ap.add_argument("--confirmations", default=None,
                    help="confirm_soundness.py verdicts (default: <out-root>/soundness-confirmations.json)")
    a = ap.parse_args()
    root = a.out_root.expanduser().absolute() if a.out_root else suite_common.default_out_root()
    RUNS = root / "runs"
    if a.confirmations is None:
        a.confirmations = str(root / "soundness-confirmations.json")
    for label in (a.label, a.z3, a.z3_events):
        if not (RUNS / label).is_dir():
            raise SystemExit(f"no run {label!r} under {RUNS}")

    z3 = load_results(a.z3)
    z3shim = load_results(a.z3_events)
    ay = load_results(a.label)
    ay_ev = load_events(a.label)
    recheck_ev = {}
    rdir = RUNS / a.label / "rechecks"
    if rdir.is_dir():
        for tdir in rdir.iterdir():
            for p in (tdir / "events").glob("*.jsonl"):
                recheck_ev.setdefault(p.stem, []).extend(
                    json.loads(l) for l in p.read_text().splitlines() if l.strip())
    z3_ev = load_events(a.z3_events)
    conf = {}
    if Path(a.confirmations).exists():
        conf = json.loads(Path(a.confirmations).read_text())
    keys = set(ay_ev) | set(z3_ev)
    out_dir = a.out_dir.expanduser().absolute() if a.out_dir else RUNS / a.label
    out_dir.mkdir(parents=True, exist_ok=True)

    # examples whose file stems collide share one event key; split_rerun.sh re-ran
    # each of them alone (with ay and with z3) into runs/<label>/split/<binary>-<test>/
    key_tests = collections.defaultdict(list)
    for k in z3:
        kk = event_key(k[0], k[1], keys)
        if kk:
            key_tests[kk].append(k)
    shared = {k for kk, v in key_tests.items() if len(v) > 1 for k in v}

    def split_events(label, k):
        d = RUNS / label / "split" / f"{k[0]}-{k[1]}" / "events"
        return [json.loads(l) for f in sorted(d.glob("*.jsonl")) for l in f.read_text().splitlines() if l.strip()] \
            if d.is_dir() else None

    def events_for(k):
        key = event_key(k[0], k[1], keys)
        ap_ = ay_ev.get(key, []) if key else []
        zp = z3_ev.get(key, []) if key else []
        src = "suite run"
        if k in shared:
            sa, sz = split_events(a.label, k), split_events(a.z3_events, k)
            if sa is not None and sz is not None:
                ap_, zp, src = sa, sz, "solo re-run (event key shared with another example)"
            else:
                src = "suite run, event key shared with another example (mixed events)"
        return key, ap_, zp, src

    # tests that are ok here: did they use the solver, and did the answers match z3?
    ok_rows = []
    for k, zr in sorted(z3.items()):
        r = ay.get(k)
        if zr["outcome"] != "ok" or r is None or r["outcome"] != "ok":
            continue
        key, ap_, zp, src = events_for(k)
        if not ap_ and not zp:
            kind = "no solver process"
        else:
            pairs, _ = pair_processes(ap_, zp)
            ds = [(diff_pair(x, y, f), x) for x, y, f in pairs]
            ds = [(d, x) for d, x in ds if d]
            if not ds:
                kind = "every answer identical to z3"
            else:
                tags = set()
                for d, x in ds:
                    if solver_errors(x):
                        tags.add("solver error")
                    elif x.get("killed"):
                        tags.add("killed at the wall")
                    else:
                        tags.add(f"{d['kind']}: z3 {d['z3']}, ay {d['ay']}")
                kind = "passes although ay diverged: " + " + ".join(sorted(tags))
        ok_rows.append({"binary": k[0], "test_name": k[1], "kind": kind, "events_from": src})
    with open(out_dir / "ok-breakdown.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["binary", "test_name", "kind", "events_from"])
        w.writeheader()
        w.writerows(ok_rows)

    rows = []
    for k, zr in sorted(z3.items()):
        if zr["outcome"] != "ok":
            continue
        r = ay.get(k)
        if r is None or r["outcome"] == "ok":
            continue
        key, ap_, zp, events_from = events_for(k)
        cls, sub, ev, divs = classify(r, ap_, zp, conf, (z3shim.get(k) or {}).get("outcome"),
                                      recheck_ev.get(key, []) if key else [])
        d0 = divs[0] if divs else None
        # soundness screen independent of query pairing: rust_verify ended without a
        # panic or signal, yet ay reported fewer invalid answers than z3 did
        clean = not re.search(r"panicked|signal", r["detail"])
        z3_inv = sum(1 for p in zp for x in p["answers"] if cat(x) in INVALID)
        ay_inv = sum(1 for p in ap_ for x in p["answers"] if cat(x) in INVALID)
        screen = "fewer-invalid-with-clean-exit" if clean and ay_inv < z3_inv else ""
        c = ev.get("confirmation") or {}
        rows.append({
            "class": cls, "subclass": sub,
            "confirmed": c.get("verdict", ""),
            "binary": k[0], "test_name": k[1], "line": r["line"], "outcome": r["outcome"],
            "event_key": key or "", "events_from": events_from,
            "query_index": d0["index"] if d0 else "", "query_hash": d0["hash"] if d0 else "",
            "z3_answer": d0["z3"] if d0 else "", "ay_answer": d0["ay"] if d0 else "",
            "ay_reason": d0.get("ay_reason", "") if d0 else "",
            "ay_secs": d0.get("ay_secs", "") if d0 else "",
            "z3_secs": d0.get("z3_secs", "") if d0 else "",
            "ay_procs": ev.get("ay_procs", 0), "z3_procs": ev.get("z3_procs", 0),
            "fuzzy_pair": bool(d0 and d0.get("fuzzy")),
            "rust_verify_clean_exit": clean, "z3_invalid_answers": z3_inv, "ay_invalid_answers": ay_inv,
            "soundness_screen": screen,
            "harness_message": r["message"][:300], "rust_verify_detail": r["detail"][:300],
            "all_classes": " ; ".join(ev.get("all_classes", [])),
            "solver_evidence": json.dumps({x: ev[x] for x in ("stderr", "errors", "rc") if x in ev})[:600],
            "exec_time_s": r["exec_time_s"],
        })
    fields = list(rows[0].keys()) if rows else ["class"]
    order = {"SOUNDNESS": 0, "SOLVER-ERROR": 1, "INCOMPLETE": 2, "PROTOCOL": 3, "OTHER": 4}
    rows.sort(key=lambda r: (order.get(r["class"], 9), r["subclass"], r["binary"], r["test_name"]))
    with open(out_dir / "classified.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)

    # every query-level difference, whether or not the test failed
    qrows = []
    for key in sorted(set(ay_ev) & set(z3_ev)):
        pairs, _ = pair_processes(ay_ev[key], z3_ev[key])
        for p, q, fz in pairs:
            d = diff_pair(p, q, fz)
            if d and d["kind"] == "answer":
                qrows.append({"event_key": key, "fuzzy_pair": fz, "ay_error": "; ".join(solver_errors(p))[:150],
                              "query_index": d["index"], "query_hash": d["hash"],
                              "z3": d["z3"], "ay": d["ay"], "z3_reason": d.get("z3_reason", ""),
                              "ay_reason": d.get("ay_reason", ""), "z3_secs": d.get("z3_secs"),
                              "ay_secs": d.get("ay_secs")})
    with open(out_dir / "query-diff.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["event_key", "fuzzy_pair", "ay_error", "query_index", "query_hash", "z3", "ay", "z3_reason",
                                          "ay_reason", "z3_secs", "ay_secs"])
        w.writeheader()
        w.writerows(qrows)

    cnt = collections.Counter(r["class"] for r in rows)
    screened = [r for r in rows if r["soundness_screen"]]
    sub = collections.Counter((r["class"], r["subclass"]) for r in rows)
    ok_here_fail_z3 = [k for k, r in ay.items() if r["outcome"] == "ok" and z3.get(k, {}).get("outcome") not in ("ok",)]
    tot = collections.Counter(r["outcome"] for r in ay.values())
    qd = collections.Counter((q["z3"], q["ay"] + (" + (error " + q["ay_error"][:60] + ")" if q["ay_error"] else ""))
                             for q in qrows)
    lines = [f"# Classification: `{a.label}` against z3 4.12.5\n",
             f"Tests in the run: {len(ay)}; outcomes: {dict(tot)}  ",
             f"Comparison set (ok on z3): {sum(1 for r in z3.values() if r['outcome'] == 'ok')}  ",
             f"Ok on z3 and not ok here: {len(rows)}  ",
             f"Ok here and not ok on z3: {len(ok_here_fail_z3)}" + (f" ({ok_here_fail_z3[:20]})" if ok_here_fail_z3 else "") + "\n",
             "## Counts per class\n", "| class | tests |", "|---|---|"]
    for c in ["SOUNDNESS", "SOLVER-ERROR", "INCOMPLETE", "PROTOCOL", "OTHER"]:
        lines.append(f"| {c} | {cnt.get(c, 0)} |")
    okc = collections.Counter(r["kind"] for r in ok_rows)
    lines += ["", "## Tests ok here (ok-breakdown.csv)\n", "| kind | tests |", "|---|---|"]
    for kk, n in okc.most_common():
        lines.append(f"| {kk} | {n} |")
    lines += ["", f"Soundness screen (rust_verify exited cleanly but ay gave fewer invalid answers than z3): "
              f"{len(screened)} tests" + (": " + ", ".join(f"{r['binary']}::{r['test_name']} ({r['class']})" for r in screened[:30]) if screened else ""),
              "", "## Subclasses\n", "| class | subclass | tests |", "|---|---|---|"]
    for (c, s), n in sorted(sub.items(), key=lambda x: (order.get(x[0][0], 9), -x[1])):
        lines.append(f"| {c} | {s.replace('|', '/')} | {n} |")
    lines += ["", "## Query-level differences (all tests, first differing answer per solver process)\n",
              "| z3 | this solver | queries |", "|---|---|---|"]
    for (z, y), n in qd.most_common():
        lines.append(f"| {z} | {y} | {n} |")
    # ay's own fail-closed model checks: stderr banners of the internal soundness gate
    gate = collections.Counter()
    gate_tests = collections.defaultdict(set)
    for key, procs in ay_ev.items():
        for p in procs:
            t = p.get("stderr_tail", "")
            for tag in ("[AY SOUNDNESS GATE]", "MODEL-UNCONFIRMED"):
                if tag in t:
                    gate[tag] += 1
                    gate_tests[tag].add(key)
    lines += ["", "## ay's internal soundness gate (stderr banners; ay fails closed to unknown)\n",
              "| banner | solver processes | tests |", "|---|---|---|"]
    for tag in ("[AY SOUNDNESS GATE]", "MODEL-UNCONFIRMED"):
        lines.append(f"| {tag} | {gate[tag]} | {len(gate_tests[tag])} |")
    lines.append("\n(the shim keeps only the last 3,000 bytes of stderr per process, so these are lower bounds)")
    (out_dir / "classified.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
