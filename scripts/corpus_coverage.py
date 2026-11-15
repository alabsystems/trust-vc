#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Per-file distance to a legitimate `ported` promotion, measured against the pinned Verus corpus.

THREE DIFFERENT NUMBERS LIVE HERE. They are not interchangeable, and only the first
one is coverage:

  1. VERIFIED coverage (the HEADLINE, printed first)
     Upstream cases the ENGINE actually reproduced: every mapped port case was RUN by the
     evidence gate's corpus lane, in a gate-accepted entry (`ported`/`unchanged`), on a path
     the gate marked `passed`, and the verdict the engine PRODUCED is upstream's verdict.
     This requires gate output (`--gate-json`); without it the script refuses to print a
     headline at all.
  2. Declaration-consistent (manifest bookkeeping, NOT coverage)
     The manifest's DECLARED `expected_verdict` agrees with upstream's verdict, the mapping
     is well formed, and the case counts line up. No engine result is consulted, so this
     number cannot move when verification regresses. Until 2026-09-16 this number was
     printed as "HEADLINE gate-accepted coverage" — it never was coverage, and the rename
     is deliberate.
  3. Scouting
     The `unsupported-gap` numerator of (2): entries the gate never schedules.

HOW TO PRODUCE GATE OUTPUT (the corpus lane; ~35 min for the full gate, less for this lane
alone; the file it writes is what `--gate-json` consumes):

    targo --unverified run --bin cargo-trust-vc -- trust-vc evidence \\
        --run-trust-vc-corpus --json --output-dir /tmp/ev
    python3 scripts/corpus_coverage.py --verus-path ../verus \\
        --gate-json /tmp/ev/replacement-evidence.json

`--declaration-only` is the explicit opt-out: it prints (2) and (3) and NO headline. There
is no silent fallback — a missing, corpus-less or unparseable gate JSON is a hard error,
because a silent fallback to (2) is exactly how the old defect survived a 3.5x collapse in
what actually passes.

Per upstream file the table reports:

  upstream   non-ignored `test_verify_one_file!` cases in the pinned upstream file
  ignored    `#[ignore]`d upstream cases (never required)
  verif      upstream cases whose every mapped port case the ENGINE ran and got upstream's
             verdict for, on a gate-`passed` path (blank without `--gate-json`)
  decl       upstream cases covered by >= 1 port case whose EVERY mapped port case DECLARES the
             upstream verdict, with EXACTLY N port cases for `assert_fails(e, N)` (upstream asserts
             `err.errors.len() == N`), and whose
             `upstream_case_id` values are bare Rust identifiers
  mism       upstream cases that are mapped but violate one of those declaration rules
  uncov      upstream cases no port case maps to
  gate       the corpus lane's verdict for this file: pass / fail / `-` (never run)

It reads the Verus checkout (default `../verus`, override with `--verus-path`), the manifest
(`evals/verus/verus-tests.json`) and, for the headline, a saved gate JSON. It never edits
anything. Counts are computed on every run; do not copy them into prose that will drift.

Verdict parsing mirrors the gate: `=> Ok(..)` is `verified`; `assert_one_fails` /
`assert_fails(e, N)` / `assert_fails_bv` are `counterexample` (with the failure count);
`assert_vir_error_msg` / `assert_rust_error_msg` / `assert_any_vir_error_msg` /
`assert_vir_error_msgs` / `assert_rust_error_msg_all` are `error`. Any other tail is
reported as `unparsed` and counted as uncovered so it can never inflate coverage. Plain
`#[test] fn` items outside the macro (harness.rs) are not enumerated here — the gate has its
own token-level extraction for them — so their manifest ids show up as `phantom`.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict

IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
MACRO_START = re.compile(r"test_verify_one_file(?:_with_options)?!\s*\{")
# `#[test]`, then any further attributes (`#[ignore]`, `#[cfg_attr(not(feature = "singular"), ignore)]`,
# …), then the case name.
TEST_NAME = re.compile(r"#\[test\]\s*((?:#\[[^\]]*\]\s*)*)([A-Za-z_][A-Za-z0-9_]*)")


def matching_brace(text: str, open_idx: int) -> int:
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
            # skip string literals (raw strings are handled coarsely: quotes inside
            # verus_code! bodies are balanced in practice)
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                i += 1
        i += 1
    return -1


def verdict_arrow(text: str) -> int:
    """Index of the verdict arrow: the first `=>` at bracket depth 0 (strings skipped) that is
    followed by `Ok(` or `Err(`; -1 when there is none."""
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                i += 1
        elif c == "=" and i + 1 < n and text[i + 1] == ">" and depth == 0:
            after = text[i + 2 :].lstrip()
            if after.startswith("Ok(") or after.startswith("Err("):
                return i
        i += 1
    return -1


def parse_verdict(tail: str, no_cheating: bool = False) -> tuple[str, int]:
    """Mirror of evidence.rs `err_helper_verdict` / `err_helper_expected_occurrences`."""
    t = tail.strip()
    if t.startswith("Ok("):
        return "verified", 0
    if not t.startswith("Err("):
        return "unparsed", 0
    body = t[t.find(")") + 1 :]
    m = re.search(r"\b(assert_[a-z_]+)\s*\(", body)
    helper = m.group(1) if m else ""
    if helper.startswith("assert_rust_error_msg") or helper.startswith("assert_vir_error_msg") \
            or helper.startswith("assert_any_vir_error_msg") or helper.startswith("assert_help_error_msg") \
            or helper in ("assert_spec_borrowed", "assert_spec_borrowed_field", "assert_spec_eq_type_err",
                          "assert_fails_type_invariant_error", "assert_custom_attr_error_msg"):
        return "error", 0
    if helper in ("assert_fails", "assert_one_fails", "assert_has_recommends_failure", "assert_expand_fails") \
            or helper.startswith("assert_fails_bv_"):
        count = 1
        if helper == "assert_fails":
            ints = re.findall(r"\b(\d+)\b", body[m.end():])
            if ints and int(ints[-1]) > 0:
                count = int(ints[-1])
        # a `--no-cheating` harness turns the cheat into a check-time rejection
        return ("error", 0) if no_cheating else ("counterexample", count)
    mm = re.search(r"err\.errors\.len\(\)\s*(?:==|,)\s*(\d+)", body) or re.search(r"assert_eq!\(\s*err\.errors\.len\(\)\s*,\s*(\d+)", body)
    if mm:
        return "counterexample", max(1, int(mm.group(1)))
    stripped = re.sub(r"/\*.*?\*/", "", body, flags=re.S).strip()
    if stripped in ("", "{}", "{ }") or stripped.startswith("todo!(") or stripped == "{ todo!() }":
        return "error", 0  # `Err(_) => {}` / `todo!()` — an unspecified rejection
    if re.search(r'contains\("(assertion failed|precondition not satisfied|postcondition not satisfied)', body):
        return "counterexample", 1
    return "unparsed", 0


def upstream_cases(path: str, no_cheating: bool = False) -> tuple[list[dict], int]:
    """Cases of one upstream file, plus the count of macro-generated blocks without a `#[test] name`."""
    text = open(path, encoding="utf-8").read()
    cases = []
    macro_generated = 0
    for m in MACRO_START.finditer(text):
        open_idx = m.end() - 1
        close_idx = matching_brace(text, open_idx)
        if close_idx < 0:
            continue
        block = text[open_idx + 1 : close_idx]
        name_m = TEST_NAME.search(block)
        if not name_m:
            macro_generated += 1
            continue
        attrs_between = name_m.group(1)
        ignored = "#[ignore" in block[: name_m.start()] or "ignore" in attrs_between
        rest = block[name_m.end() :]
        arrow = verdict_arrow(rest)
        tail = rest[arrow + 2 :] if arrow >= 0 else ""
        verdict, count = parse_verdict(tail, no_cheating)
        cases.append({"id": name_m.group(2), "ignored": ignored, "verdict": verdict, "failures": count})
    return cases, macro_generated



# Gate-accepted classifications: the only entries the evidence gate schedules and checks.
ACCEPTED_CLASSIFICATIONS = ("ported", "unchanged")


class GateOutputError(Exception):
    """A gate JSON that cannot answer the headline question. Never downgraded to a warning."""


def load_gate_corpus(path: str) -> tuple[dict, dict]:
    """Return (per-upstream-path corpus result, provenance) from a saved evidence-gate JSON.

    Every failure here is FATAL on purpose. The headline is a claim about what the engine
    produced; with no engine output there is no honest number to print, and falling back to
    the declaration count is the defect this function exists to prevent.
    """
    try:
        with open(path, encoding="utf-8") as handle:
            report = json.load(handle)
    except FileNotFoundError as err:
        raise GateOutputError(f"gate JSON not found: {path}") from err
    except (OSError, json.JSONDecodeError) as err:
        raise GateOutputError(f"gate JSON unreadable ({path}): {err}") from err
    if not isinstance(report, dict) or "trust_vc_corpus" not in report:
        raise GateOutputError(
            f"{path} is not an evidence-gate report (no `trust_vc_corpus` key). "
            "Produce one with `trust-vc evidence --run-trust-vc-corpus --json`."
        )
    corpus = report.get("trust_vc_corpus")
    if corpus is None:
        raise GateOutputError(
            f"{path} was produced WITHOUT the corpus lane (`trust_vc_corpus` is null), so it "
            "records no engine verdict for any port case. Re-run the gate with "
            "`--run-trust-vc-corpus`."
        )
    results = corpus.get("results") or []
    if not results:
        raise GateOutputError(f"{path} ran the corpus lane but recorded zero path results.")
    # ONE upstream file can produce SEVERAL path results (a direct-source port plus a cargo
    # fixture, say), so this is a list per upstream path, never a single result — keying it
    # by path alone silently kept the last one and threw away the others' verdicts.
    by_path: dict[str, list[dict]] = defaultdict(list)
    for result in results:
        by_path[result["upstream_path"]].append(result)
    repo = report.get("repository") or {}
    provenance = {
        "gate_json": os.path.abspath(path),
        "generated_unix_seconds": report.get("generated_unix_seconds"),
        "trust_vc_head": repo.get("trust_vc_head"),
        "dirty": repo.get("dirty"),
        "strict": report.get("strict"),
        "attempted_paths": corpus.get("attempted_paths"),
        "passed_paths": corpus.get("passed_paths"),
        "failed_paths": corpus.get("failed_paths"),
        "skipped_entries": corpus.get("skipped_entries"),
    }
    return by_path, provenance


def observed_verdicts(results: list[dict]) -> dict[str, list[tuple[str, str]]]:
    """port case id -> every (verdict, owning path status) the gate recorded for it."""
    seen: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for result in results:
        status = result.get("status", "")
        for case in result.get("observed_cases") or []:
            seen[case["case_id"]].append((case.get("verdict", ""), status))
    return seen


def gate_staleness_warnings(provenance: dict, manifest_path: str) -> list[str]:
    """Reasons the saved gate JSON may not describe THIS tree. Printed, never silently dropped."""
    warnings = []
    generated = provenance.get("generated_unix_seconds")
    if generated:
        try:
            manifest_mtime = os.path.getmtime(manifest_path)
        except OSError:
            manifest_mtime = 0
        if manifest_mtime > generated:
            warnings.append(
                "the manifest has been modified SINCE this gate run, so the mapping measured "
                "here may not be the mapping the gate ran"
            )
    head = None
    try:
        head = subprocess.run(
            ["/usr/bin/git", "rev-parse", "HEAD"],
            cwd=os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
            capture_output=True,
            text=True,
            check=False,
        ).stdout.strip()
    except OSError:
        head = None
    recorded = provenance.get("trust_vc_head")
    if head and recorded and not recorded.startswith(head) and not head.startswith(recorded):
        warnings.append(f"gate run was at `{recorded}`; this worktree is at `{head}`")
    if provenance.get("dirty"):
        warnings.append("the gate run was made from a DIRTY worktree")
    return warnings


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--verus-path", default=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "..", "verus"))
    ap.add_argument("--manifest", default=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "evals", "verus", "verus-tests.json"))
    ap.add_argument("--json", action="store_true", help="emit machine-readable rows instead of the table")
    ap.add_argument("--only", help="restrict to entries whose upstream_path contains this substring")
    ap.add_argument("--show-uncovered", action="store_true", help="list uncovered / mismatched upstream ids per file")
    ap.add_argument("--accepted-only", action="store_true", help="restrict the table to gate-accepted entries (classification ported/unchanged)")
    ap.add_argument(
        "--gate-json",
        help="saved evidence-gate report (`trust-vc evidence --run-trust-vc-corpus --json`, "
        "default output `<crate_root>/.trust_vc/evidence/replacement-evidence.json`). REQUIRED "
        "for the VERIFIED headline: it is the only input that records what the engine produced.",
    )
    ap.add_argument(
        "--declaration-only",
        action="store_true",
        help="explicitly ask for the manifest-only numbers and NO headline. Without this the "
        "script refuses to run with no --gate-json rather than silently printing bookkeeping.",
    )
    ap.add_argument(
        "--show-unverified",
        action="store_true",
        help="with --gate-json, list per file the declaration-consistent upstream ids the engine "
        "did NOT reproduce, and why",
    )
    args = ap.parse_args()

    if not args.gate_json and not args.declaration_only:
        print(
            "corpus_coverage.py: REFUSING to print a coverage number with no gate output.\n"
            "\n"
            "  The VERIFIED headline is a claim about what the engine PRODUCED. This script's\n"
            "  manifest-only count is a declaration-consistency check and is NOT coverage; it\n"
            "  was printed as the headline until 2026-09-16 and survived a 3.5x collapse in what\n"
            "  actually passes without moving. There is no silent fallback any more.\n"
            "\n"
            "  Produce gate output:\n"
            "    targo --unverified run --bin cargo-trust-vc -- trust-vc evidence \\\n"
            "        --run-trust-vc-corpus --json --output-dir /tmp/ev\n"
            "  then pass it:\n"
            "    python3 scripts/corpus_coverage.py --verus-path ../verus \\\n"
            "        --gate-json /tmp/ev/replacement-evidence.json\n"
            "\n"
            "  Or ask for the weak number BY NAME: --declaration-only\n",
            file=sys.stderr,
        )
        return 2

    gate_by_path: dict = {}
    provenance: dict = {}
    stale: list[str] = []
    if args.gate_json:
        try:
            gate_by_path, provenance = load_gate_corpus(args.gate_json)
        except GateOutputError as err:
            print(f"corpus_coverage.py: {err}", file=sys.stderr)
            return 2
        stale = gate_staleness_warnings(provenance, args.manifest)

    manifest = json.load(open(args.manifest, encoding="utf-8"))
    rows = []
    for entry in manifest["entries"]:
        up = entry["upstream_path"]
        if args.only and args.only not in up:
            continue
        if not up.startswith("source/rust_verify_test/tests/") or "/cargo-tests/" in up:
            continue
        if args.accepted_only and entry["classification"] not in ACCEPTED_CLASSIFICATIONS:
            continue
        path = os.path.join(args.verus_path, up)
        if not os.path.exists(path):
            rows.append({"file": up, "classification": entry["classification"], "missing_upstream": True})
            continue
        no_cheating = any("--no-cheating" in str(a) for a in (entry.get("trust_vc_check_args") or []))
        cases, macro_generated = upstream_cases(path, no_cheating)
        by_id = {c["id"]: c for c in cases}
        mapped: dict[str, list[dict]] = defaultdict(list)
        for pc in entry.get("expected_cases") or []:
            uid = pc.get("upstream_case_id") or pc["case_id"]
            mapped[uid].append(pc)
        gate_results = gate_by_path.get(up) or []
        if not gate_results:
            gate_status = None
        elif all(r.get("status") == "passed" for r in gate_results):
            gate_status = "passed"
        else:
            gate_status = "failed"
        accepted_entry = entry["classification"] in ACCEPTED_CLASSIFICATIONS
        # Only a path the gate marked `passed` can carry verified coverage: on a failed path
        # the engine's own per-case verdict may be right while the case is rejected for a
        # reason the observed verdict does not record (a missing FAILS marker, an unmatched
        # diagnostic, a surplus obligation).
        produced = observed_verdicts(gate_results)
        clean, mismatch, uncovered, unparsed = [], [], [], []
        verified, unverified, split_entry_verified = [], [], []
        for c in cases:
            if c["ignored"]:
                continue
            if c["verdict"] == "unparsed":
                unparsed.append(c["id"])
                continue
            pcs = mapped.get(c["id"])
            if not pcs:
                uncovered.append(c["id"])
                continue
            ok = all(pc["expected_verdict"] == c["verdict"] for pc in pcs)
            ok = ok and all(IDENT.match(pc.get("upstream_case_id") or pc["case_id"]) for pc in pcs)
            # Upstream assert_fails(e, N) is assert_eq!(err.errors.len(), N):
            # EXACTLY N failures, spent on exactly N mapped port cases.
            if c["verdict"] == "counterexample" and len(pcs) != c["failures"]:
                ok = False
            if c["verdict"] != "error" and any(pc.get("min_obligations", 0) == 0 for pc in pcs):
                ok = False
            (clean if ok else mismatch).append(c["id"])
            if not args.gate_json:
                continue
            # VERIFIED: the engine ran EVERY mapped port case on a green path and produced
            # upstream's own verdict for each. A port case the run never observed, or observed
            # with a different verdict, disqualifies the upstream case.
            why = None
            if not ok:
                why = "declaration-inconsistent"
            elif not accepted_entry:
                why = f"`{entry['classification']}` entry — the gate never accepts it as evidence"
            elif not gate_results:
                why = "never run by the gate"
            else:
                for pc in pcs:
                    got = produced.get(pc["case_id"])
                    if not got:
                        why = f"port case `{pc['case_id']}` produced no engine verdict"
                        break
                    if any(v != c["verdict"] for v, _ in got):
                        why = (
                            f"port case `{pc['case_id']}` produced "
                            f"{sorted({v for v, _ in got})}, upstream wants `{c['verdict']}`"
                        )
                        break
                    if any(status != "passed" for _, status in got):
                        why = f"port case `{pc['case_id']}` ran on a path the gate FAILED"
                        break
            if why is None:
                verified.append(c["id"])
                if gate_status != "passed":
                    split_entry_verified.append(c["id"])
            elif ok:
                unverified.append(f"{c['id']}: {why}")
        phantom = sorted(uid for uid in mapped if uid not in by_id)
        rows.append(
            {
                "file": up.split("/")[-1],
                "classification": entry["classification"],
                "upstream": sum(1 for c in cases if not c["ignored"]),
                "ignored": sum(1 for c in cases if c["ignored"]),
                "verified": len(verified),
                "clean": len(clean),
                "mismatch": len(mismatch),
                "uncovered": len(uncovered) + len(unparsed),
                "unparsed": len(unparsed),
                "phantom_ids": len(phantom),
                "macro_generated": macro_generated,
                "port_cases": len(entry.get("expected_cases") or []),
                "gate_status": gate_status,
                "gate_paths": len(gate_results),
                "gate_execution_modes": sorted({r.get("execution_mode", "") for r in gate_results}),
                "verified_in_split_entry": len(split_entry_verified),
                "_detail": {
                    "mismatch": mismatch,
                    "uncovered": uncovered,
                    "unparsed": unparsed,
                    "phantom": phantom,
                    "unverified": unverified,
                },
            }
        )

    rows.sort(key=lambda r: (r.get("uncovered", 0) + r.get("mismatch", 0), -r.get("upstream", 0)))
    if args.json:
        tot = totals(rows)
        for r in rows:
            r.pop("_detail", None)
        block = headline_block(tot, bool(args.gate_json))
        # A restricted run MUST say so in the machine-readable channel too. The text
        # output prints a NOTE; without this the JSON of `--only option.rs` is
        # `verified_pct: 100.0` and is indistinguishable from a full-corpus run, which
        # is exactly the quote-out-of-context defect this script was rebuilt to stop.
        restricted = bool(args.only or args.accepted_only)
        block["denominator_restricted"] = restricted
        block["restricted_by"] = (
            {"only": args.only, "accepted_only": bool(args.accepted_only)} if restricted else None
        )
        payload = {
            "gate": provenance or None,
            "gate_staleness_warnings": stale,
            "denominator_restricted": restricted,
            "restricted_by": block["restricted_by"],
            "headline": block,
            "rows": rows,
        }
        json.dump(payload, sys.stdout, indent=2)
        print()
        return 0

    gate_col = " gate" if args.gate_json else ""
    verif_col = " verif" if args.gate_json else ""
    hdr = f"{'file':34} {'class':16} {'upstr':>5} {'ign':>3}{verif_col:>6} {'decl':>5} {'mism':>4} {'uncov':>5} {'phant':>5} {'cases':>5}{gate_col:>5}"
    print(hdr)
    print("-" * len(hdr))
    for r in rows:
        if r.get("missing_upstream"):
            print(f"{r['file']:34} {r['classification']:16} (upstream file missing at --verus-path)")
            continue
        verif = f" {r['verified']:5d}" if args.gate_json else ""
        gate = ""
        if args.gate_json:
            gate = {"passed": " pass", "failed": " fail", "skipped": " skip"}.get(r["gate_status"], "    -")
        print(
            f"{r['file']:34} {r['classification']:16} {r['upstream']:5d} {r['ignored']:3d}{verif} {r['clean']:5d} {r['mismatch']:4d} {r['uncovered']:5d} {r['phantom_ids']:5d} {r['port_cases']:5d}{gate}"
        )
        if args.show_uncovered and (r["_detail"]["mismatch"] or r["_detail"]["uncovered"] or r["_detail"]["phantom"]):
            for k in ("mismatch", "uncovered", "unparsed", "phantom"):
                if r["_detail"][k]:
                    print(f"    {k}: {', '.join(r['_detail'][k])}")
        if args.show_unverified and r["_detail"]["unverified"]:
            for line in r["_detail"]["unverified"]:
                print(f"    unverified {line}")
    tot = totals(rows)
    print("-" * len(hdr))
    verif_tot = f" {tot['verified']:5d}" if args.gate_json else ""
    print(
        f"{'TOTAL (' + str(tot['files']) + ' files)':51} {tot['upstream']:5d} {tot['ignored']:3d}{verif_tot} {tot['clean']:5d} {tot['mismatch']:4d} {tot['uncovered']:5d} {tot['phantom_ids']:5d} {tot['port_cases']:5d}"
    )
    if not tot["upstream"]:
        return 0
    block = headline_block(tot, bool(args.gate_json))
    print()
    if args.accepted_only or args.only:
        print(
            "NOTE: --accepted-only/--only RESTRICT the denominator below to the rows shown. The "
            "corpus-wide number needs an unrestricted run."
        )
    if args.gate_json:
        print(
            f"HEADLINE VERIFIED coverage (engine produced upstream's verdict): "
            f"{block['verified']} / {block['denominator']} = {block['verified_pct']:.2f}%"
        )
        print(
            f"  measured from {provenance['gate_json']}: corpus lane ran {provenance['attempted_paths']} paths, "
            f"{provenance['passed_paths']} passed, {provenance['failed_paths']} failed, "
            f"{provenance['skipped_entries']} skipped; gate HEAD {provenance['trust_vc_head']}, "
            f"dirty={provenance['dirty']}, strict={provenance['strict']}"
        )
        print(
            f"  a case counts only when the gate RAN every mapped port case on a `passed` path in a "
            f"{'/'.join(ACCEPTED_CLASSIFICATIONS)} entry and the ENGINE returned upstream's verdict."
        )
        if tot["verified_in_split_entry"]:
            print(
                f"  {tot['verified_in_split_entry']} of them sit in an entry that ALSO has a failing "
                "sibling path (one upstream file, several gate paths); the gate accepts the entry "
                "only when every one of its paths passes, so the entry-level number is "
                f"{block['verified'] - tot['verified_in_split_entry']}."
            )
        for warning in stale:
            print(f"  STALE-GATE WARNING: {warning}")
    else:
        print(
            "HEADLINE VERIFIED coverage: NOT MEASURED (--declaration-only). No gate output was "
            "read, so nothing below is a coverage number."
        )
    print()
    print(
        f"Declaration-consistent (manifest bookkeeping, NOT coverage): "
        f"{block['declaration_consistent_accepted']} / {block['denominator']} = "
        f"{block['declaration_consistent_accepted_pct']:.2f}%"
    )
    print(
        "  compares the MANIFEST's declared verdict against upstream's and never asks whether "
        "trust-vc produced it; it cannot move when verification regresses."
    )
    print(
        f"  all entries {tot['clean']} / {tot['upstream']} = {100.0 * tot['clean'] / tot['upstream']:.2f}%"
        f"  (accepted entries' own denominator {block['accepted_denominator']};"
        f" unparsed tails {tot['unparsed']}, macro-generated blocks not enumerated {tot['macro_generated']})"
    )
    print()
    print(
        f"Scouting (declaration-consistent rows in unsupported-gap entries the gate never "
        f"schedules): {block['scouting']} / {tot['upstream_unsupported-gap']}"
    )
    # Printed LAST and unconditionally, including under --declaration-only: every
    # accepted number above is an accepted number, and none of them may leave this
    # script without the fraction that is PROGRAM-correspondence SCOPED, nor that
    # fraction without the smaller one it ESTABLISHES, nor either of them without
    # the LAYER-1 statement that upstream is read for every accepted case.
    print_accepted_case_split(accepted_case_split(manifest))
    return 0


def accepted_case_split(manifest: dict) -> dict:
    """The manifest's accepted expected cases, split by WHAT PINS EACH ONE to upstream.

    A fourth number, and the one that qualifies every other accepted count printed here.
    THERE ARE TWO LAYERS. LAYER 1 runs for EVERY accepted case, but its SUB-CHECKS DO NOT
    SHARE THAT DENOMINATOR, and round 9's finding was this docstring and the block below
    writing as though they did. Corpus-wide, on every accepted case: the gate's per-case
    upstream block reads the upstream file, resolves the declared upstream case, and
    requires the DECLARED verdict to equal upstream's. Narrower, each on its own
    population: the mapped-case count is compared per UPSTREAM case and is EXACT only
    where upstream states a failure count; every message upstream asserts must be declared
    (and, in the run lane, appear in the port's own diagnostic) only for the error cases
    whose upstream case asserts one; and the warning, forbidden-pattern and cargo-fixture
    checks each run on a handful of cases. The manifest's own `correspondence_bound`
    prints every one of those populations beside its check; this script does not restate
    them, because a second copy of a denominator is a second thing to drift.
    LAYER 2 is the source-level correspondence rule over the port's PROGRAM, and it
    governs COUNTEREXAMPLE cases only: `append_counterexample_identity_failures` returns
    on its second line for any other expected verdict, so a `verified` case is tied to
    upstream by an obligation COUNT and an engine-derived fingerprint of the PORT'S OWN
    obligations, and nothing reads upstream's PROGRAM for it.

    Until round 8 this docstring and the block it prints said a verified case was tied to
    upstream by nothing that reads upstream's source. That was FALSE, and pessimistic:
    the split below is what each layer covers, not whether upstream is read at all.
    Printing an accepted-case number without the split reads as "this many cases had
    their program checked against upstream".

    The `verified` bucket is split again, because "pinned by an obligation COUNT" is
    FALSE for part of it. For a `cargo_trust_vc_integration_test` entry the manifest
    schema REQUIRES `verified` with `min_obligations: 0` and REFUSES any fingerprints,
    and the gate never invokes the engine for those cases at all, so the count records
    no author decision. Those rows are reported separately as SCHEMA-FIXED.

    The full statement is the manifest's own top-level `correspondence_bound`, which the
    gate refuses to load if it differs from the constant in `evidence.rs` by one byte.
    """
    split: dict = {"counterexample": 0, "verified": 0, "error": 0, "other": 0}
    split["verified_schema_fixed"] = 0
    for entry in manifest["entries"]:
        if entry["classification"] not in ACCEPTED_CLASSIFICATIONS:
            continue
        schema_fixed = entry.get("evidence_kind") == "cargo_trust_vc_integration_test"
        for case in entry.get("expected_cases", []):
            verdict = case.get("expected_verdict", "other")
            split[verdict if verdict in split else "other"] += 1
            if schema_fixed:
                split["verified_schema_fixed"] += 1
    split["total"] = sum(
        split[k] for k in ("counterexample", "verified", "error", "other")
    )
    split["verified_author_pinned"] = split["verified"] - split["verified_schema_fixed"]
    split["headline"] = correspondence_bound_headline(manifest)
    return split


def print_accepted_case_split(split: dict) -> None:
    total = split["total"]
    if not total:
        return
    pct = lambda n: 100.0 * n / total
    print()
    print(
        f"Accepted expected cases (manifest): {total} — ALL {total} are LAYER-1 checked "
        f"against upstream, in the two checks that run on every one of them (the declared "
        f"upstream case RESOLVES, and the declared verdict EQUALS upstream's); the mapped-case "
        f"count, upstream-asserted messages, warning and forbidden patterns are checked too but "
        f"on smaller populations, which the manifest's `correspondence_bound` prints beside each. "
        f"Of the {total}, "
        f"{split['counterexample']} ({pct(split['counterexample']):.1f}%) are additionally "
        f"PROGRAM-CORRESPONDENCE SCOPED (LAYER 2, the only bucket whose SOURCE is compared "
        f"with upstream's; how many of them that rule actually ESTABLISHES is the headline "
        f"below, and it is smaller), "
        f"{split['verified']} ({pct(split['verified']):.1f}%) are pinned by an obligation COUNT "
        f"and the port's OWN fingerprints only, establishing NOTHING about the port's PROGRAM "
        f"({split['verified_author_pinned']} of them; the other "
        f"{split['verified_schema_fixed']} are SCHEMA-FIXED "
        f"`cargo_trust_vc_integration_test` rows whose verdict and zero count the schema "
        f"writes, so they are pinned by nothing at all), and "
        f"{split['error']} ({pct(split['error']):.1f}%) by diagnostic patterns plus, where "
        f"upstream asserts a message, upstream's own string."
    )
    print(
        f"  Only the counterexample bucket enters the gate's PROGRAM-level correspondence rule, "
        f"so {pct(split['counterexample']):.1f}% is the fraction of accepted cases whose source "
        "was compared with upstream's — a SCOPE, not a result, and NOT the fraction for which "
        "upstream was read at all, which is 100%. Inside that fraction the rule still does "
        "not discriminate block structure or statement order (both channels are SETS)."
    )
    headline = split.get("headline", "")
    if headline:
        # Quoted from the manifest's own `correspondence_bound`, never recomputed
        # here: the established half is measured by the gate against the pinned
        # Verus checkout, and a second implementation of that measurement in this
        # script is exactly how two numbers start disagreeing.
        print()
        print("  " + headline)
    print(
        "  Read the manifest's `correspondence_bound` in full before quoting any number on "
        "this page."
    )


def correspondence_bound_headline(manifest: dict) -> str:
    """The one sentence of the manifest's `correspondence_bound` a reader will quote.

    Verbatim, from the manifest. This script recomputes the SCOPE split above from the
    entries; it deliberately does not recompute the ESTABLISHED half, which the gate
    measures against the pinned Verus checkout with its own readers.
    """
    bound = manifest.get("correspondence_bound", "")
    start = bound.find("HEADLINE:")
    if start < 0:
        return ""
    end = bound.find("EVERY BUCKET BELOW", start)
    return bound[start:end].strip() if end > start else bound[start:].strip()


def totals(rows: list[dict]) -> defaultdict:
    tot: defaultdict = defaultdict(int)
    for r in rows:
        if r.get("missing_upstream"):
            continue
        for k in ("upstream", "ignored", "verified", "verified_in_split_entry", "clean", "mismatch", "uncovered", "unparsed", "phantom_ids", "port_cases", "macro_generated"):
            tot[k] += r[k]
        tot["files"] += 1
        tot["clean_" + r["classification"]] += r["clean"]
        tot["verified_" + r["classification"]] += r["verified"]
        tot["upstream_" + r["classification"]] += r["upstream"]
    return tot


def headline_block(tot: defaultdict, have_gate: bool) -> dict:
    denominator = tot["upstream"]
    accepted_clean = sum(tot["clean_" + c] for c in ACCEPTED_CLASSIFICATIONS)
    verified = sum(tot["verified_" + c] for c in ACCEPTED_CLASSIFICATIONS)
    return {
        "denominator": denominator,
        "accepted_denominator": sum(tot["upstream_" + c] for c in ACCEPTED_CLASSIFICATIONS),
        "verified": verified if have_gate else None,
        "verified_pct": (100.0 * verified / denominator) if (have_gate and denominator) else None,
        "verified_measured": have_gate,
        "declaration_consistent_accepted": accepted_clean,
        "declaration_consistent_accepted_pct": (100.0 * accepted_clean / denominator) if denominator else 0.0,
        "declaration_consistent_all_entries": tot["clean"],
        "scouting": tot["clean_unsupported-gap"],
        "verified_in_split_entry": tot["verified_in_split_entry"] if have_gate else None,
        "verified_entry_level": (verified - tot["verified_in_split_entry"]) if have_gate else None,
    }


if __name__ == "__main__":
    sys.exit(main())
