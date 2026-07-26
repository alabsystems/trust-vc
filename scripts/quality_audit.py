#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Small repository quality audit for tracked files.

The audit intentionally uses only Python's standard library so it can run in a
fresh checkout. It checks Git-tracked files for editor/build cruft, leaked local
paths, oversized Rust source files, and production Rust panic-style escapes.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


DEFAULT_MAX_RUST_LINES = 500
MAX_FINDINGS_PER_GROUP = 40
ALLOW_PREFIX = "quality-audit:"
TEST_PATH_PARTS = {"benches", "examples", "fuzz", "tests"}
EVIDENCE_FIXTURE_PREFIXES = (("evals", "verus", "ported"),)
SRC_TEST_MODULE_RE = re.compile(r"^(?:tests?|tests_.*)\.rs$")
SRC_TEST_MODULE_DIR_RE = re.compile(r"^(?:tests_.*|.*_tests)$")


@dataclass(frozen=True)
class Finding:
    group: str
    path: str
    message: str
    line: int | None = None

    def location(self) -> str:
        if self.line is None:
            return self.path
        return f"{self.path}:{self.line}"


@dataclass(frozen=True)
class ContentPattern:
    label: str
    regex: re.Pattern[str]


CRUFT_PATH_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("macOS Finder metadata", re.compile(r"(^|/)\.DS_Store$")),
    ("Windows thumbnail metadata", re.compile(r"(^|/)Thumbs\.db$")),
    ("Windows desktop metadata", re.compile(r"(^|/)Desktop\.ini$")),
    ("Python bytecode/cache", re.compile(r"(^|/)(__pycache__|.*\.(pyc|pyo))$")),
    ("Python tool cache", re.compile(r"(^|/)\.(pytest_cache|mypy_cache|ruff_cache)(/|$)")),
    ("Rust build output", re.compile(r"(^|/)target(/|$)")),
    ("JavaScript dependencies", re.compile(r"(^|/)node_modules(/|$)")),
    ("IDE workspace metadata", re.compile(r"(^|/)\.(idea|vscode)(/|$)")),
    ("local environment file", re.compile(r"(^|/)\.env(\..*)?$")),
    ("editor swap/backup file", re.compile(r"(^|/)[^/].*(~|\.sw[op]|\.tmp|\.bak|\.orig|\.rej)$")),
    ("log file", re.compile(r"(^|/)[^/]+\.log$")),
)


LOCAL_PATH_PATTERNS: tuple[ContentPattern, ...] = (
    ContentPattern(
        "macOS user-home path",
        re.compile(
            "/" "Users" r"/(?!(?:user|test|example|runner|ci|sandbox)(?:/|$))"
            r"[A-Za-z0-9._-]+/"
        ),
    ),
    ContentPattern(
        "Linux user-home path",
        re.compile(
            "/" "home" r"/(?!(?:user|test|example|runner|ci|sandbox)(?:/|$))"
            r"[A-Za-z0-9._-]+/"
        ),
    ),
    ContentPattern(
        "Windows user-home path",
        re.compile(
            r"[A-Za-z]:\\Users\\"
            r"(?!(?:user|test|example|runner|ci|sandbox)(?:\\|$))[^\\/\s]+\\"
        ),
    ),
    ContentPattern("Drop" "box path", re.compile(r"\bDrop" "box" r"\b")),
    ContentPattern("One" "Drive path", re.compile(r"\bOne" "Drive" r"\b")),
    ContentPattern("Google " "Drive path", re.compile(r"\bGoogle " "Drive" r"\b")),
    ContentPattern("i" "Cloud " "Drive path", re.compile(r"\bi" "Cloud " "Drive" r"\b")),
    ContentPattern("Apple Cloud" "Storage path", re.compile(r"\bCloud" "Storage" r"\b")),
    ContentPattern("Apple Mobile " "Documents path", re.compile(r"\bMobile " "Documents" r"\b")),
)


PRODUCTION_POLICY_RE = re.compile(
    r"\.(?P<method>unwrap|expect)\s*\(|\b(?P<macro>panic|todo)\s*!\s*\("
)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit tracked repository files for common quality hazards."
    )
    parser.add_argument(
        "--max-rust-lines",
        type=int,
        default=int(os.environ.get("QUALITY_AUDIT_MAX_RUST_LINES", DEFAULT_MAX_RUST_LINES)),
        help=(
            "maximum allowed lines in a tracked .rs file "
            f"(default: {DEFAULT_MAX_RUST_LINES}; env: QUALITY_AUDIT_MAX_RUST_LINES)"
        ),
    )
    parser.add_argument(
        "--strict-tests",
        action="store_true",
        help="also enforce unwrap/expect/panic/todo policy in test, example, bench, and fuzz code",
    )
    parser.add_argument(
        "--skip-rust-size",
        action="store_true",
        help="skip oversized Rust source checks",
    )
    parser.add_argument(
        "--skip-production-policy",
        action="store_true",
        help="skip unwrap/expect/panic/todo checks",
    )
    parser.add_argument(
        "--max-findings",
        type=int,
        default=MAX_FINDINGS_PER_GROUP,
        help=f"maximum findings printed per group (default: {MAX_FINDINGS_PER_GROUP})",
    )
    return parser.parse_args(argv)


def repo_root() -> Path:
    result = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        return Path(result.stdout.strip())
    return Path(__file__).resolve().parent.parent


def git_tracked_files(root: Path) -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        sys.stderr.write(result.stderr.decode("utf-8", errors="replace"))
        raise SystemExit(result.returncode)
    return [part.decode("utf-8", errors="replace") for part in result.stdout.split(b"\0") if part]


def read_text(path: Path) -> str | None:
    try:
        data = path.read_bytes()
    except OSError:
        return None
    if b"\0" in data:
        return None
    return data.decode("utf-8", errors="replace")


def file_allow_markers(text: str) -> set[str]:
    markers: set[str] = set()
    for line in text.splitlines()[:40]:
        marker = marker_from_line(line)
        if marker:
            markers.update(marker.split())
    return markers


def marker_from_line(line: str) -> str:
    marker_index = line.find(ALLOW_PREFIX)
    if marker_index < 0:
        return ""
    return line[marker_index + len(ALLOW_PREFIX) :].strip()


def allows(markers: Iterable[str], *keys: str) -> bool:
    marker_set = set(markers)
    return "allow-all" in marker_set or any(key in marker_set for key in keys)


def is_test_like_path(path: str) -> bool:
    path_obj = Path(path)
    parts = path_obj.parts
    name = path_obj.name
    return (
        bool(set(parts) & TEST_PATH_PARTS)
        or parts[:3] in EVIDENCE_FIXTURE_PREFIXES
        or name.endswith(("_test.rs", "_tests.rs"))
        or is_src_test_module_file(parts, name)
    )


def is_src_test_module_file(parts: tuple[str, ...], name: str) -> bool:
    try:
        src_index = parts.index("src")
    except ValueError:
        return False
    if SRC_TEST_MODULE_RE.fullmatch(name):
        return len(parts) > src_index + 1
    return any(SRC_TEST_MODULE_DIR_RE.match(part) for part in parts[src_index + 1 : -1])


def audit_cruft_paths(paths: list[str]) -> list[Finding]:
    findings: list[Finding] = []
    for path in paths:
        for label, pattern in CRUFT_PATH_PATTERNS:
            if pattern.search(path):
                findings.append(Finding("tracked cruft", path, label))
                break
    return findings


def audit_local_paths(root: Path, paths: list[str]) -> list[Finding]:
    findings: list[Finding] = []
    for rel_path in paths:
        text = read_text(root / rel_path)
        if text is None:
            continue
        file_markers = file_allow_markers(text)
        if allows(file_markers, "allow-file", "allow-local-paths"):
            continue
        previous_marker = ""
        for line_number, line in enumerate(text.splitlines(), start=1):
            current_marker = marker_from_line(line)
            markers = f"{previous_marker} {current_marker}".split()
            previous_marker = current_marker
            if allows(markers, "allow-line", "allow-local-path", "allow-local-paths"):
                continue
            for pattern in LOCAL_PATH_PATTERNS:
                if pattern.regex.search(line):
                    findings.append(Finding("local path leakage", rel_path, pattern.label, line_number))
                    break
    return findings


def audit_rust_size(root: Path, paths: list[str], max_rust_lines: int) -> list[Finding]:
    if max_rust_lines <= 0:
        return []
    findings: list[Finding] = []
    for rel_path in paths:
        if not rel_path.endswith(".rs"):
            continue
        text = read_text(root / rel_path)
        if text is None:
            continue
        if allows(file_allow_markers(text), "allow-file", "allow-rust-size"):
            continue
        line_count = len(text.splitlines())
        if line_count > max_rust_lines:
            findings.append(
                Finding(
                    "oversized Rust source",
                    rel_path,
                    f"{line_count} lines exceeds threshold {max_rust_lines}",
                )
            )
    return findings


def masked_rust_lines(text: str) -> list[str]:
    lines: list[str] = []
    in_block_comment = False
    in_string = False
    raw_string_hashes: int | None = None

    for line in text.splitlines():
        output: list[str] = []
        index = 0
        while index < len(line):
            char = line[index]
            next_char = line[index + 1] if index + 1 < len(line) else ""

            if in_block_comment:
                if char == "*" and next_char == "/":
                    output.extend("  ")
                    index += 2
                    in_block_comment = False
                else:
                    output.append(" ")
                    index += 1
                continue

            if raw_string_hashes is not None:
                terminator = '"' + ("#" * raw_string_hashes)
                if line.startswith(terminator, index):
                    output.extend(" " * len(terminator))
                    index += len(terminator)
                    raw_string_hashes = None
                else:
                    output.append(" ")
                    index += 1
                continue

            if in_string:
                if char == "\\":
                    output.extend("  " if next_char else " ")
                    index += 2 if next_char else 1
                elif char == '"':
                    output.append(" ")
                    index += 1
                    in_string = False
                else:
                    output.append(" ")
                    index += 1
                continue

            if char == "/" and next_char == "/":
                output.extend(" " * (len(line) - index))
                break
            if char == "/" and next_char == "*":
                output.extend("  ")
                index += 2
                in_block_comment = True
                continue
            if char == '"':
                output.append(" ")
                index += 1
                in_string = True
                continue
            if char == "r":
                raw_match = re.match(r'r(#{0,255})"', line[index:])
                if raw_match:
                    raw_string_hashes = len(raw_match.group(1))
                    token_len = 2 + raw_string_hashes
                    output.extend(" " * token_len)
                    index += token_len
                    continue

            output.append(char)
            index += 1
        lines.append("".join(output))
    return lines


def rust_test_line_mask(raw_lines: list[str], code_lines: list[str], path_is_test_like: bool) -> list[bool]:
    if path_is_test_like:
        return [True] * len(raw_lines)

    tail_test_start = cfg_test_tail_module_start(raw_lines, code_lines)
    mask: list[bool] = []
    cfg_test_attr_pending = False
    cfg_test_item_pending = False
    test_depths: list[int] = []
    depth = 0

    for line_index, (raw_line, code_line) in enumerate(zip(raw_lines, code_lines)):
        if tail_test_start is not None and line_index >= tail_test_start:
            mask.append(True)
            continue

        while test_depths and depth < test_depths[-1]:
            test_depths.pop()

        stripped_raw = raw_line.strip()
        stripped_code = code_line.strip()
        if stripped_raw.startswith("#[cfg(test"):
            cfg_test_attr_pending = True

        entering_test_module = False
        cfg_test_line = False
        if cfg_test_item_pending:
            cfg_test_line = True
            if "{" in stripped_code:
                entering_test_module = True
                cfg_test_item_pending = False
            elif ";" in stripped_code:
                cfg_test_item_pending = False
        elif cfg_test_attr_pending and stripped_code and not stripped_code.startswith("#["):
            cfg_test_line = True
            if "{" in stripped_code:
                entering_test_module = True
                cfg_test_attr_pending = False
            elif ";" in stripped_code:
                cfg_test_attr_pending = False
            elif re.search(
                r"\b(fn|mod|impl|const|static|struct|enum|type|trait|macro_rules)\b",
                stripped_code,
            ):
                cfg_test_item_pending = True
                cfg_test_attr_pending = False
            else:
                cfg_test_attr_pending = False

        line_is_test = bool(test_depths) or entering_test_module or cfg_test_line
        mask.append(line_is_test)

        delta = code_line.count("{") - code_line.count("}")
        depth = max(0, depth + delta)
        if entering_test_module:
            test_depths.append(depth)

    return mask


def cfg_test_tail_module_start(raw_lines: list[str], code_lines: list[str]) -> int | None:
    for line_index, raw_line in enumerate(raw_lines):
        if not raw_line.strip().startswith("#[cfg(test"):
            continue
        for candidate_index in range(line_index + 1, min(line_index + 4, len(code_lines))):
            stripped = raw_lines[candidate_index].strip()
            if not stripped or stripped.startswith("#["):
                continue
            if re.search(r"\bmod\s+tests\b", stripped) and "{" in stripped:
                return line_index
            break
    return None


def audit_production_policy(root: Path, paths: list[str], strict_tests: bool) -> list[Finding]:
    findings: list[Finding] = []
    for rel_path in paths:
        if not rel_path.endswith(".rs"):
            continue
        text = read_text(root / rel_path)
        if text is None:
            continue
        file_markers = file_allow_markers(text)
        if allows(file_markers, "allow-file", "allow-production-policy"):
            continue

        raw_lines = text.splitlines()
        code_lines = masked_rust_lines(text)
        test_lines = rust_test_line_mask(raw_lines, code_lines, is_test_like_path(rel_path))
        previous_marker = ""

        for line_number, (raw_line, code_line, is_test_line) in enumerate(
            zip(raw_lines, code_lines, test_lines), start=1
        ):
            current_marker = marker_from_line(raw_line)
            markers = f"{previous_marker} {current_marker}".split()
            previous_marker = current_marker

            if is_test_line and not strict_tests:
                continue

            for match in PRODUCTION_POLICY_RE.finditer(code_line):
                policy = match.group("method") or match.group("macro") or "policy"
                if allows(
                    markers,
                    "allow-line",
                    "allow-production-policy",
                    f"allow-{policy}",
                ):
                    continue
                findings.append(
                    Finding(
                        "production unwrap/expect/panic/todo",
                        rel_path,
                        f"{policy} is not allowed outside test code",
                        line_number,
                    )
                )
    return findings


def print_findings(findings: list[Finding], max_findings: int) -> None:
    if not findings:
        print("quality audit passed")
        return

    print(f"quality audit failed: {len(findings)} finding(s)")
    groups = list(dict.fromkeys(finding.group for finding in findings))
    for group in groups:
        group_findings = [finding for finding in findings if finding.group == group]
        print(f"\n[{group}] {len(group_findings)} finding(s)")
        for finding in group_findings[:max_findings]:
            print(f"  {finding.location()}: {finding.message}")
        remaining = len(group_findings) - max_findings
        if remaining > 0:
            print(f"  ... {remaining} more not shown; rerun with --max-findings to expand")

    print(
        "\nAllow intentional exceptions with a nearby comment like "
        "`quality-audit: allow-production-policy`, or a file-header "
        "`quality-audit: allow-file allow-rust-size` marker."
    )


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    root = repo_root()
    paths = git_tracked_files(root)

    findings: list[Finding] = []
    findings.extend(audit_cruft_paths(paths))
    findings.extend(audit_local_paths(root, paths))
    if not args.skip_rust_size:
        findings.extend(audit_rust_size(root, paths, args.max_rust_lines))
    if not args.skip_production_policy:
        findings.extend(audit_production_policy(root, paths, args.strict_tests))

    print_findings(findings, args.max_findings)
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
