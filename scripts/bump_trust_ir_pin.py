#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""Move the three IR pins, lock, binding labels and real fixtures atomically.

Run through build-slot with an explicit genuine Targo. The target object store
is read-only; Cargo resolves its immutable revision. Existing fixture producers
derive identities, and any failed guard restores every controlled file. This
is an unverified development transaction, never a proof or release attestation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tempfile
import time
import tomllib

from pin_git import ObjectStore, environment as git_environment


IR = "https://github.com/alabsystems/trust-ir.git"
AY = "https://github.com/alabsystems/ay.git"
AY_CRATES = ("ay-core", "ay-dpll", "ay-frontend", "ay-sys")
ENGINE = "crates/trust-vc-trust-engine"
BODY = f"{ENGINE}/fixtures/trust_ir_body"
NATIVE = f"{ENGINE}/fixtures/trust_ir_native"
BINDING = f"{ENGINE}/src/trust_ir_body/binding.rs"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def atomic(path: Path, data: bytes, mode: int) -> None:
    # Cargo watches these inputs. Equal bytes and permissions must retain their
    # identity and timestamp instead of invalidating the same dependency graph.
    try:
        current = path.lstat()
        if (stat.S_ISREG(current.st_mode) and current.st_nlink == 1
                and stat.S_IMODE(current.st_mode) == mode and path.read_bytes() == data):
            return
    except FileNotFoundError:
        pass
    descriptor, temporary = tempfile.mkstemp(prefix=".ir-pin-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as out:
            out.write(data)
            os.fchmod(out.fileno(), mode)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("revision")
    parser.add_argument("--ir-git-dir", required=True, type=Path)
    parser.add_argument("--targo", required=True, type=Path)
    parser.add_argument("--evidence-dir", required=True, type=Path)
    args = parser.parse_args()
    require(re.fullmatch(r"[0-9a-f]{40}", args.revision) is not None, "full immutable IR revision required")
    require(args.targo.is_absolute() and args.targo.is_file(), "explicit absolute genuine Targo required")
    root = Path(__file__).resolve().parents[1]
    out = args.evidence_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    record = {"revision": args.revision, "classification": "unverified development source-cohort transaction", "runs": []}

    def save() -> None:
        (out / "record.json").write_text(json.dumps(record, indent=2) + "\n")

    def git(*arguments: str) -> str:
        return subprocess.check_output(["git", *arguments], cwd=root, text=True, env=git_environment()).strip()

    store = None

    def target(path: str) -> bytes:
        nonlocal store
        if store is None:
            store = ObjectStore(args.ir_git_dir, args.revision)
        return store.read(path)

    def run(arguments: list[str], cwd: Path = root, *, allow_failure: bool = False) -> subprocess.CompletedProcess:
        start = time.monotonic()
        index = len(record["runs"])
        command = [str(args.targo), *arguments]
        item = {"argv": command, "cwd": str(cwd)}
        record["runs"].append(item)
        stdout = out / f"{index:02d}.stdout"
        stderr = out / f"{index:02d}.stderr"
        with stdout.open("wb") as output, stderr.open("wb") as errors:
            child = subprocess.Popen(command, cwd=cwd, stdout=output, stderr=errors)
            item.update(pid=child.pid, running=True)
            save()
            code = child.wait()
        result = subprocess.CompletedProcess(command, code, stdout.read_bytes(), stderr.read_bytes())
        item.update(exit=code, running=False, seconds=time.monotonic() - start)
        save()
        print(f"{arguments[0]}: exit {result.returncode}, {time.monotonic() - start:.2f}s", flush=True)
        require(allow_failure or result.returncode == 0, f"command failed; see {out}/{index:02d}.stderr")
        return result

    run(["--unverified", "--version"])
    doc = tomllib.loads((root / "Cargo.toml").read_text())
    deps = doc["workspace"]["dependencies"]
    revisions = {deps[name]["rev"] for name in ["trust-ir", "trust-ir-build", "trust-ir-contract"]}
    require(len(revisions) == 1, "the three current IR legs disagree")
    require(all(deps[name].get("git") == IR for name in ["trust-ir", "trust-ir-build", "trust-ir-contract"]), "IR authority changed")
    old = revisions.pop()
    ay_revisions = {deps[name]["rev"] for name in AY_CRATES}
    ay_versions = {deps[name]["version"] for name in AY_CRATES}
    require(len(ay_revisions) == 1 and len(ay_versions) == 1, "AY legs disagree")
    ay_revision = next(iter(ay_revisions))
    ay_version = next(iter(ay_versions))
    require(re.fullmatch(r"[0-9a-f]{40}", ay_revision) is not None, "immutable AY revision required")
    require(all(deps[name].get("git") == AY and "path" not in deps[name] for name in AY_CRATES), "AY authority changed")
    version = tomllib.loads(target("Cargo.toml").decode())["workspace"]["package"]["version"]
    wire = int(re.search(rb"pub const VERSION: u32 = (\d+);", target("crates/trust-ir/src/binary.rs"))[1])
    schema = int(re.search(rb"NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION: u32 = (\d+);", target("crates/trust-ir/src/request/consts.rs"))[1])
    clean = tomllib.loads(target("crates/trust-ir/Cargo.toml").decode())["dependencies"]["clean-kernel"]["rev"]
    locks = [Path(name) for name in git("ls-files", "*Cargo.lock").splitlines()]
    controlled = [Path("Cargo.toml"), *locks, Path(BINDING), *[path.relative_to(root) for directory in [BODY, NATIVE] for path in (root / directory).glob("*") if path.is_file()]]
    before = {}
    for name in controlled:
        path = root / name
        require(path.is_file() and not path.is_symlink() and path.stat().st_nlink == 1, f"unsafe controlled path: {name}")
        before[name] = (path.read_bytes(), stat.S_IMODE(path.stat().st_mode))
    record.update(old_revision=old, version=version, wire=wire, bundle_schema=schema, clean_predecessor=clean, ay_revision=ay_revision, head=git("rev-parse", "HEAD"), before_sha256={str(name): hashlib.sha256(data).hexdigest() for name, (data, _) in before.items()})
    watched = set(git("diff", "--name-only").splitlines()) | set(git("ls-files", "--others", "--exclude-standard").splitlines())
    source_hashes = {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in sorted(watched) if Path(name) not in before}
    record["source_sha256"] = source_hashes
    save()

    def write(name: str, data: bytes) -> None:
        path = Path(name)
        atomic(root / path, data, before[path][1])

    def test(name: str, filter_name: str | None = None, runtime_env: str | None = None, allow_failure: bool = False):
        selection = ["--lib"] if name == "lib" else ["--test", name]
        arguments = ["--unverified", "test", "--locked", "-p", "trust-vc-trust-engine", "--features", "proof-certificates", *selection]
        if runtime_env:
            # Native SDKs may keep compiler and tool binaries in separate
            # directories. Query the compiler selected for this transaction.
            compiler = os.environ.get("RUSTC", str(args.targo.parent / "trustc"))
            host = subprocess.check_output([compiler, "-vV"], text=True)
            triple = re.search(r"^host: (.+)$", host, re.M)[1]
            arguments += ["--config", f"target.{triple}.runner={json.dumps(['/usr/bin/env', runtime_env + '=1'])}"]
        arguments += ["--", *([filter_name] if filter_name else []), "--test-threads=1"]
        result = run(arguments, allow_failure=allow_failure)
        if result.returncode == 0:
            text = result.stdout.decode()
            require(re.search(r"test result: ok\. [1-9]\d* passed; 0 failed; 0 ignored;", text) is not None, f"missing nonvacuous test census: {name}")
        return result

    try:
        manifest = before[Path("Cargo.toml")][0]
        require(manifest.count(old.encode()) == 3, "unexpected current pin occurrences")
        write("Cargo.toml", manifest.replace(old.encode(), args.revision.encode()))
        binding = before[Path(BINDING)][0]
        old_label = re.search(rb"trust-ir ([^\"]+) bin v(\d+)", binding)
        require(old_label is not None, "missing binding pin label")
        previous_label = old_label[1].decode()
        label = f"{version}@{args.revision}"
        write(BINDING, binding.replace(old_label[0], f"trust-ir {label} bin v{wire}".encode()))
        readme = before[Path(f"{BODY}/README.md")][0].decode().replace(previous_label, label)
        readme = re.sub(r"\(binary format v\d+, bundle schema v\d+\)", f"(binary format v{wire}, bundle schema v{schema})", readme)
        write(f"{BODY}/README.md", readme.encode())
        readme = before[Path(f"{NATIVE}/README.md")][0].decode()
        readme = re.sub(r"rev `[0-9a-f]{40}`", f"rev `{args.revision}`", readme, count=1)
        readme = re.sub(r"bundle schema \d+", f"bundle schema {schema}", readme, count=1)
        write(f"{NATIVE}/README.md", readme.encode())
        canonical = target("crates/trust-ir-conformance/tests/fixtures/native_request_trust_bundle.json")
        write(f"{NATIVE}/native_request_trust_bundle.json", canonical)
        metadata = run(["metadata", "--format-version", "1"])
        require(b"was not used" not in metadata.stderr, "unused root dependency patch")
        resolved = json.loads(metadata.stdout)["packages"]
        require(all(f"#{args.revision}" in package["source"] for package in resolved if package["name"].startswith("trust-ir") and package["source"]), "mixed IR authority")
        require(all(f"#{clean}" in package["source"] for package in resolved if package["name"].startswith("clean-") and package["source"]), "mixed Clean predecessor authority")
        ay_packages = [package for package in resolved if package["name"].startswith("ay-")]
        require(set(AY_CRATES).issubset({package["name"] for package in ay_packages}), "missing direct AY packages")
        require(all(package["source"] == f"git+{AY}?rev={ay_revision}#{ay_revision}" and package["version"] == ay_version for package in ay_packages), "mixed or redirected AY authority")
        for lock in locks:
            if lock != Path("Cargo.lock"):
                run(["metadata", "--format-version", "1"], root / lock.parent)
            previous = tomllib.loads(before[lock][0].decode())
            current = tomllib.loads((root / lock).read_text())
            external = lambda value: sorted((json.dumps(package, sort_keys=True) for package in value.get("package", []) if not package["name"].startswith(("trust-ir", "clean-"))))
            require(external(previous) == external(current), f"unrelated package resolution changed: {lock}")
        run(["--unverified", "check", "--locked", "-p", "trust-vc-trust-engine", "--all-targets", "--features", "proof-certificates"])
        first = test("trust_ir_body_discharge", "the_checked_in_fixture_matches_the_builder", "TRUST_VC_REGEN_TRUST_IR_BODY_FIXTURES", True)
        require(first.returncode == 0 or (root / BODY / "guarded_checked_add_u8.json").read_bytes() != before[Path(f"{BODY}/guarded_checked_add_u8.json")][0], "fixture regeneration failed without a changed fixture")
        test("trust_ir_body_discharge", "the_checked_in_fixture_matches_the_builder")
        test("native_trust_ir_bundle", "regenerate_discharge_fixtures", "TRUST_VC_REGENERATE_DISCHARGE_FIXTURES")
        test("trust_ir_pin_label")
        test("trust_ir_runtime_closure")
        test("lib", "unused_runtime_closure_declines_before_relational_lowering")
        test("lib", "producer_fields::tests")
        test("trust_ir_body_certificate")
        run(["metadata", "--locked", "--format-version", "1"])
        require((root / NATIVE / "native_request_trust_bundle.json").read_bytes() == canonical, "canonical native fixture changed during guards")
        require(all(hashlib.sha256((root / name).read_bytes()).hexdigest() == value for name, value in source_hashes.items()), "source changed during qualification")
        record.update(exit=0, terminal=True, after_sha256={str(name): hashlib.sha256((root / name).read_bytes()).hexdigest() for name in before})
        save()
    except BaseException as error:
        for name, (data, mode) in before.items():
            atomic(root / name, data, mode)
        record.update(exit=1, terminal=True, error=repr(error), restored=True)
        save()
        raise


if __name__ == "__main__":
    main()
