# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Scoring for a trust-vc run of the upstream suite.

A trust-vc run stages trust-vc-rustc's rust_verify where the harness looks for
Verus's. The harness only sees diagnostics and an exit code, so a harness pass
alone says nothing about whether trust-vc did the work. Every rust_verify run
therefore writes a verdict record (one JSON line per run, schema
trust-vc.verdict@1) to TRUST_VC_VERDICT_DIR/<test dir>.jsonl, naming every
function it saw and what it concluded. This module joins each libtest result
with those records and with the diagnostics of a Verus+z3 reference run, and
gives every test one score:

  pass            the harness passed it, a record exists, nothing was refused,
                  and every function called verified agrees with the reference.
  refused         a record or a diagnostic carries "trust-vc refused: <tag>"
                  (or a function is recorded refused or skipped). Counted as
                  refused even when the harness passed it.
  false-pass      the harness passed it and there is no record. Must be 0.
  vacuous         the harness passed it, there is no record, and the reference
                  run has no capture either: the test ran no rust_verify under
                  either front end (examples.rs's "ignore" files return before
                  running anything). Neither a pass nor a failure of trust-vc.
  false-pass-ref  a function recorded verified holds a line where the reference
                  run reports an error. Must be 0, and wins over every other
                  score: it is a verification claim that Verus+z3 contradicts.
  bad-record      a record line is not JSON, or a record calls a function
                  refused or skipped without any refusal diagnostic in the run
                  (the harness would have seen a clean run). Must be 0.
  untagged-fail   the harness did not pass it and nothing was refused. Must be 0.
  ignored         #[ignore] in the test source.
  not-run         the runner did not run it (an excluded binary).

A function called verified in a test with no reference capture, or whose
capture holds an error without a primary span, cannot be cross-checked; it is
counted as unchecked-verified, which must also be 0.

The reference is a run of the same runner with --capture-diagnostics, which
copies every rust_verify run's stderr to diags/<test dir>/<n>.stderr, headed
by an "entry=<entry file>" line and ended by an "exit=<code>" line.

The test dir is the directory the harness makes for each test and passes as
rustc's -o directory: <binary>-<test> for the test_verify_one_file! cases and
example-<file stem> for examples.rs, whose tests pass an entry file from the
examples tree. Two examples can share a file stem, so their records and
captures are told apart by entry file.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

REFUSAL = "trust-vc refused: "
TAG_RE = re.compile(re.escape(REFUSAL) + r"([a-z0-9][a-z0-9-]*)")
ABORTING_RE = re.compile(r"^aborting due to")

SCORES = ["pass", "refused", "false-pass", "false-pass-ref", "bad-record", "untagged-fail",
          "vacuous", "ignored", "not-run"]
# Scores that make a run not ok.
BAD_SCORES = ["false-pass", "false-pass-ref", "bad-record", "untagged-fail"]

EXAMPLES_MACRO_RE = re.compile(r'^\s*examples_in_dir!\("([^"]+)"\);', re.M)


# --------------------------------------------------------------------------- test dirs

def example_tests(verus_src: Path) -> dict:
    """examples.rs test name -> (test dir, entry file as the harness passes it).

    Mirrors rust_verify_test_macros' examples_in_dir!: the test is named after
    the directory (relative to rust_verify/, "../../" dropped, "/" and "-" made
    "_") and the file prefix (up to the first dot, "-" made "_"); the harness
    runs <dir>/<file> from rust_verify_test/ with -o in test_inputs/example-<file
    stem>."""
    src = verus_src / "rust_verify_test" / "tests" / "examples.rs"
    if not src.is_file():
        return {}
    out = {}
    for rel in EXAMPLES_MACRO_RE.findall(src.read_text()):
        under = rel.replace("../../", "").replace("/", "_").replace("-", "_")
        directory = (verus_src / "rust_verify" / rel).resolve()
        if not directory.is_dir():
            continue
        for f in sorted(directory.iterdir()):
            if f.suffix != ".rs":
                continue
            prefix = f.name.split(".", 1)[0]
            out[f"{under}_{prefix.replace('-', '_')}"] = (f"example-{f.stem}", f"{rel}/{f.name}")
    return out


def test_dir_of(binary: str, test: str, examples: dict):
    """(test dir, entry file or None) for one libtest test."""
    if binary == "examples" and test in examples:
        return examples[test]
    return f"{binary}-{test}", None


def norm_file(path: str) -> str:
    """A source file named relative to its test: the part after
    test_inputs/<test dir>/, else the part from examples/, else the base name.
    Both runs stage the same files under different roots."""
    m = re.search(r"/test_inputs/[^/]+/(.+)$", path)
    if m:
        return m.group(1)
    m = re.search(r"(?:^|/)(examples/.+)$", path)
    if m:
        return m.group(1)
    return Path(path).name


# --------------------------------------------------------------------------- records

def read_records(verdict_dir: Path, test_dir: str, entry: str | None):
    """The verdict records of one test. A line that is not JSON is returned as
    {"corrupt": line}. With `entry`, only records of that entry file."""
    path = verdict_dir / f"{test_dir}.jsonl"
    if not path.exists():
        return []
    recs = []
    for line in path.read_text(errors="replace").splitlines():
        if not line.strip():
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            recs.append({"corrupt": line[:200]})
            continue
        if entry is not None and rec.get("entry_file") != entry:
            continue
        recs.append(rec)
    return recs


def refusal_tags(records, texts=()):
    """Refusal tags of a test, from its records and from any diagnostic text
    (the libtest output of a failed test)."""
    tags = set()
    for r in records:
        for f in r.get("functions", []):
            if f.get("verdict") in ("refused", "skipped"):
                tags.add(f.get("tag") or "untagged")
        for m in r.get("crate_refusals", []):
            hit = TAG_RE.match(m)
            tags.add(hit.group(1) if hit else "untagged")
        if r.get("refused") and not tags:
            tags.add("untagged")
    for text in texts:
        tags.update(TAG_RE.findall(text or ""))
    return sorted(tags)


# --------------------------------------------------------------------------- reference

def reference_captures(ref_dir: Path, test_dir: str, entry: str | None):
    """The reference run's stderr captures of one test, as a list of
    (entry, text). None when the test has no capture at all."""
    d = ref_dir / "diags" / test_dir
    if not d.is_dir():
        return None
    caps = []
    for f in sorted(d.glob("*.stderr")):
        lines = f.read_text(errors="replace").splitlines()
        head = lines[0] if lines else ""
        cap_entry = head[len("entry="):] if head.startswith("entry=") else None
        if entry is not None and cap_entry != entry:
            continue
        caps.append((cap_entry, "\n".join(lines[1:] if cap_entry is not None else lines)))
    return caps if caps or entry is None else None


def reference_errors(captures):
    """(sites, unplaced) from the reference captures: every (file, line) of an
    error's primary spans, which is where Verus puts the failing site (the
    assertion, the call whose precondition failed, the failed postcondition,
    the overflowing operation), and the number of errors without one."""
    sites, unplaced = set(), 0
    for _, text in captures:
        for line in text.splitlines():
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(d, dict) or d.get("level") != "error":
                continue
            if ABORTING_RE.match(d.get("message", "")):
                continue
            placed = [(norm_file(sp.get("file_name", "")), sp["line_start"])
                      for sp in d.get("spans", []) if sp.get("is_primary")]
            if placed:
                sites.update(placed)
            else:
                unplaced += 1
    return sites, unplaced


def cross_check(records, reference):
    """(false passes, unchecked) among the functions recorded verified.
    `reference` is (sites, unplaced) or None when there is no capture."""
    false_pass, unchecked = [], []
    for r in records:
        for f in r.get("functions", []):
            if f.get("verdict") != "verified":
                continue
            span = f.get("lines")
            if reference is None or not span:
                unchecked.append(f.get("def_path", "?"))
                continue
            sites, unplaced = reference
            if unplaced:
                unchecked.append(f.get("def_path", "?"))
                continue
            file = norm_file(f.get("file") or "")
            if any((not file or site_file == file) and span[0] <= line <= span[1]
                   for site_file, line in sites):
                false_pass.append(f.get("def_path", "?"))
    return false_pass, unchecked


# --------------------------------------------------------------------------- one test

def unaccounted_refusal(record) -> bool:
    """A function recorded refused or skipped in a run that emitted no refusal
    diagnostic: every such function must be backed by one, or the harness can
    take the run for a clean one."""
    not_verified = any(f.get("verdict") in ("refused", "skipped") for f in record.get("functions", []))
    return not_verified and not record.get("crate_refusals")


def score_test(harness: str, records, texts, reference, reference_ran=None):
    """The score of one test and its details. `reference_ran` is False when
    the reference run has no capture for the test (it ran no rust_verify),
    None when that is unknown (no reference)."""
    tags = refusal_tags(records, texts)
    verified = [f for r in records for f in r.get("functions", []) if f.get("verdict") == "verified"]
    refused_fns = [f for r in records for f in r.get("functions", [])
                   if f.get("verdict") in ("refused", "skipped")]
    false_ref, unchecked = cross_check(records, reference)
    if harness == "ignored":
        score = "ignored"
    elif harness == "not-run":
        score = "not-run"
    elif false_ref:
        score = "false-pass-ref"
    elif any("corrupt" in r or unaccounted_refusal(r) for r in records):
        score = "bad-record"
    elif tags:
        score = "refused"
    elif harness == "ok" and records:
        score = "pass"
    elif harness == "ok":
        score = "vacuous" if reference_ran is False else "false-pass"
    else:
        score = "untagged-fail"
    sites_proved = sum(f.get("sites_proved") or 0 for f in verified)
    sites_failed = sum(f.get("sites_failed") or 0
                       for r in records for f in r.get("functions", []))
    return {
        "score": score,
        "tags": " ".join(tags),
        "records": len(records),
        "verified_fns": len(verified),
        "refused_fns": len(refused_fns),
        "sites_proved": sites_proved,
        "sites_failed": sites_failed,
        "false_pass_ref_fns": " ".join(false_ref),
        "unchecked_verified_fns": 0 if score in ("ignored", "not-run", "vacuous") else len(unchecked),
        "compiler_commits": sorted({r.get("compiler_commit") for r in records
                                    if r.get("compiler_commit")}),
    }


# --------------------------------------------------------------------------- libtest output

def failed_test_output(logs_dir: Path, binary: str) -> dict:
    """test name -> libtest's captured output of its last failed attempt, read
    from the runner's logs/<binary>.a<n>.jsonl streams."""
    out = {}

    def attempt_no(p):
        m = re.search(r"\.a(\d+)\.jsonl$", p.name)
        return int(m.group(1)) if m else 0

    for f in sorted(logs_dir.glob(f"{binary}.a*.jsonl"), key=attempt_no):
        for line in f.read_text(errors="replace").splitlines():
            try:
                e = json.loads(line)
            except json.JSONDecodeError:
                continue
            if e.get("type") == "test" and e.get("event") == "failed":
                out[e.get("name")] = e.get("stdout", "")
    return out


# --------------------------------------------------------------------------- a run

def ordinary_test_entry(file, test_dir):
    """The normal harness's exact input suffix, without resolving files."""
    if (not isinstance(file, str) or not file or not isinstance(test_dir, str)
            or not test_dir or "/" in test_dir or test_dir in (".", "..")):
        return False
    path = Path(file)
    return (path.is_absolute() and str(path) == file and ".." not in path.parts
            and path.parts[-3:] == ("test_inputs", test_dir, "test.rs"))


def reference_rejection_match(records, reference, reference_ran, reference_outcome,
                              test_dir, entry, captures, native_entry):
    """Recognize two recorded compiler rejections despite a red reference harness.

    This establishes rejection coverage, not identical diagnostic causes. No
    accepted or verified function can use this exception to the coverage guard.
    Every native record must have a real source range covering a placed error
    from the reference. Unknown shapes retain the ordinary conservative guard.
    """
    if (reference_outcome != "FAILED" or reference_ran is not True or reference is None
            or not records or entry is not None or not captures):
        return False
    sites, unplaced = reference
    if type(unplaced) is not int or unplaced != 0 or not sites:
        return False
    if any(not isinstance(file, str) or not file or type(line) is not int or line < 1
           for file, line in sites):
        return False
    for reference_entry, text in captures:
        if not ordinary_test_entry(reference_entry, test_dir) or not isinstance(text, str):
            return False
        lines = [line for line in text.splitlines() if line.strip()]
        if not lines or lines[-1] != "exit=1":
            return False
        for line in lines:
            try:
                diagnostic = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(diagnostic, dict) or diagnostic.get("level") != "error":
                continue
            if ABORTING_RE.match(diagnostic.get("message", "")):
                continue
            primary = [span for span in diagnostic.get("spans", []) if span.get("is_primary") is True]
            if not primary or any(span.get("file_name") != reference_entry for span in primary):
                return False
    for record in records:
        if (not isinstance(record, dict) or "corrupt" in record
                or record.get("schema") != "trust-vc.verdict@1"
                or record.get("outcome") != "verus-rejected"
                or type(record.get("exit_code")) is not int or record["exit_code"] != 1
                or "erase_exit" not in record or record["erase_exit"] is not None
                or not ordinary_test_entry(record.get("entry_file"), test_dir)
                or record["entry_file"] != native_entry
                or not isinstance(record.get("compiler_commit"), str)
                or re.fullmatch(r"[0-9a-f]{40}", record["compiler_commit"]) is None
                or record.get("refused") is not False or record.get("crate_refusals") != []):
            return False
        functions = record.get("functions")
        if not isinstance(functions, list) or not functions:
            return False
        matched = False
        for function in functions:
            if (not isinstance(function, dict)
                    or function.get("verdict") not in ("rejected", "external")
                    or function.get("kind") not in ("Fn", "AssocFn", "Const", "AssocConst")
                    or not isinstance(function.get("def_path"), str) or not function["def_path"].strip()
                    or "tag" not in function or function["tag"] is not None):
                return False
            for key in ("sites_proved", "sites_failed"):
                if key not in function or not (function[key] is None
                        or type(function[key]) is int and function[key] == 0):
                    return False
            file, span = function.get("file"), function.get("lines")
            if (file != record["entry_file"] or not isinstance(span, list) or len(span) != 2
                    or any(type(line) is not int or line < 1 for line in span) or span[0] > span[1]):
                return False
            file = norm_file(file)
            if not file:
                return False
            matched |= any(site_file == file and span[0] <= line <= span[1] for site_file, line in sites)
        if not matched:
            return False
    return True


def score_run(rows, verdict_dir: Path, logs_dir: Path, verus_src: Path, reference_dir: Path | None,
              reference_outcomes: dict | None):
    """Score every row of a run's results (the dicts load_results makes).
    Returns (per-test rows, totals)."""
    examples = example_tests(verus_src)
    outputs = {}
    scored = []
    for r in rows:
        binary, test = r["binary"], r["test_name"]
        if binary not in outputs:
            outputs[binary] = failed_test_output(logs_dir, binary)
        test_dir, entry = test_dir_of(binary, test, examples)
        records = read_records(verdict_dir, test_dir, entry)
        reference, reference_ran, caps = None, None, None
        if reference_dir is not None:
            caps = reference_captures(reference_dir, test_dir, entry)
            reference_ran = caps is not None
            if caps is not None:
                reference = reference_errors(caps)
        ref_outcome = (reference_outcomes or {}).get((binary, test), "")
        if reference_ran is False and ref_outcome != "ok":
            reference_ran = None  # a reference that did not pass the test says nothing about it
        s = score_test(r["outcome"], records, [outputs[binary].get(test, "")], reference, reference_ran)
        s["reference_rejection_match"] = 0
        if s["score"] == "pass" and reference_outcomes is not None and ref_outcome != "ok":
            native_entry = (verdict_dir.parent / "stage/source/target.noindex/debug/test_inputs"
                            / test_dir / "test.rs")
            if reference_rejection_match(records, reference, reference_ran, ref_outcome,
                                         test_dir, entry, caps, str(native_entry)):
                # Both compilers rejected before verification. Keep the red
                # reference harness visible without inventing a verified fn.
                s["reference_rejection_match"] = 1
            else:
                s["unchecked_verified_fns"] = max(s["unchecked_verified_fns"], 1)
        scored.append({
            "binary": binary, "test_name": test, "test_dir": test_dir, "harness": r["outcome"],
            "reference": ref_outcome, **{k: v for k, v in s.items() if k != "compiler_commits"},
            "_commits": s["compiler_commits"],
        })
    totals = summarize(scored)
    commits = sorted({c for s in scored for c in s["_commits"]})
    for s in scored:
        del s["_commits"]
    totals["compiler_commits"] = commits
    return scored, totals


def summarize(scored):
    count = {k: 0 for k in SCORES}
    for s in scored:
        count[s["score"]] += 1
    live = sum(1 for s in scored if s["score"] not in ("ignored", "not-run"))
    totals = {
        "listed": len(scored),
        "live": live,
        "pass": count["pass"],
        "refused": count["refused"],
        "vacuous": count["vacuous"],
        "refused_but_harness_ok": sum(1 for s in scored if s["score"] == "refused" and s["harness"] == "ok"),
        "false_pass": count["false-pass"],
        "false_pass_ref": count["false-pass-ref"],
        "bad_record": count["bad-record"],
        "untagged_fail": count["untagged-fail"],
        "ignored": count["ignored"],
        "not_run": count["not-run"],
        "verified_fns": sum(s["verified_fns"] for s in scored),
        "unchecked_verified_fns": sum(s["unchecked_verified_fns"] for s in scored),
        "reference_rejection_matches": sum(s.get("reference_rejection_match", 0) for s in scored),
        "sites_proved_in_passes": sum(s["sites_proved"] for s in scored if s["score"] == "pass"),
        "sites_failed_in_passes": sum(s["sites_failed"] for s in scored if s["score"] == "pass"),
    }
    totals["ok"] = (all(count[k] == 0 for k in BAD_SCORES) and totals["unchecked_verified_fns"] == 0)
    tags = {}
    for s in scored:
        for t in s["tags"].split():
            tags[t] = tags.get(t, 0) + 1
    totals["tags"] = dict(sorted(tags.items(), key=lambda kv: (-kv[1], kv[0])))
    return totals


SCORE_FIELDS = ["binary", "test_name", "test_dir", "harness", "reference", "score", "tags", "records",
                "verified_fns", "refused_fns", "sites_proved", "sites_failed", "false_pass_ref_fns",
                "unchecked_verified_fns", "reference_rejection_match"]


def summary_lines(scored, totals, per_binary=True):
    """Markdown lines for summary.md."""
    lines = ["## trust-vc score\n",
             "| | tests |", "|---|---|"]
    for k, v in totals.items():
        if k in ("tags", "compiler_commits"):
            continue
        lines.append(f"| {k} | {v} |")
    lines.append("")
    lines.append(f"Compiler commit(s) in the verdict records: {', '.join(totals['compiler_commits']) or 'none'}\n")
    lines.append("Refusal tags (tests carrying each):\n")
    lines += [f"- `{t}`: {n}" for t, n in totals["tags"].items()] or ["- none"]
    lines.append("")
    if per_binary:
        by = {}
        for s in scored:
            b = by.setdefault(s["binary"], {k: 0 for k in SCORES})
            b[s["score"]] += 1
        lines.append("| file | " + " | ".join(SCORES) + " |")
        lines.append("|---|" + "---|" * len(SCORES))
        for name in sorted(by):
            lines.append(f"| {name}.rs | " + " | ".join(str(by[name][k]) for k in SCORES) + " |")
        lines.append("")
    odd = [s for s in scored if s["score"] in BAD_SCORES or s["unchecked_verified_fns"]]
    lines.append(f"Tests that break the run ({len(odd)}):\n")
    lines += [f"- {s['binary']}::{s['test_name']}: {s['score']} (harness {s['harness']})"
              + (f", false pass in {s['false_pass_ref_fns']}" if s["false_pass_ref_fns"] else "")
              + (f", {s['unchecked_verified_fns']} unchecked verified" if s["unchecked_verified_fns"] else "")
              for s in odd] or ["- none"]
    lines.append("")
    return lines
