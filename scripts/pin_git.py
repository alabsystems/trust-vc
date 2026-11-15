#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Read-only Git object integrity for the caller-selected immutable IR store.

This checks exact bytes. Public-main qualification remains the caller's duty;
it grants no compiler, proof, native or release verdict.
"""
import hashlib
import os
from pathlib import Path
import re
import subprocess


def environment():
    result = dict(os.environ)
    for key in list(result):
        if key.startswith("GIT_CONFIG") or key in {
            "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
            "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE",
            "GIT_REPLACE_REF_BASE", "GIT_GRAFT_FILE", "GIT_SHALLOW_FILE", "GIT_TEMPLATE_DIR",
            "GIT_DEFAULT_HASH", "GIT_DEFAULT_REF_FORMAT",
        }:
            del result[key]
    result.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                  GIT_NO_REPLACE_OBJECTS="1", GIT_GRAFT_FILE=os.devnull,
                  GIT_NO_LAZY_FETCH="1", GIT_ALLOW_PROTOCOL="file",
                  GIT_TERMINAL_PROMPT="0", GIT_OPTIONAL_LOCKS="0")
    return result


class ObjectStore:
    def __init__(self, directory, revision):
        if re.fullmatch(r"[0-9a-f]{40}", revision) is None:
            raise RuntimeError("full immutable IR revision required")
        self.directory = Path(directory)
        commit = self.object("commit", revision)
        match = re.match(rb"tree ([0-9a-f]{40})\n", commit)
        if match is None:
            raise RuntimeError("IR commit has no canonical root tree")
        self.tree = match[1].decode("ascii")

    @staticmethod
    def tree_entries(raw):
        at, names = 0, set()
        while at < len(raw):
            space, zero = raw.find(b" ", at), raw.find(b"\0", at)
            if not (at < space < zero and zero + 21 <= len(raw)):
                raise RuntimeError("malformed immutable IR tree")
            mode, name = raw[at:space], raw[space + 1:zero]
            if not name or b"/" in name or name in {b".", b".."} or name in names:
                raise RuntimeError("ambiguous immutable IR tree name")
            names.add(name)
            yield mode, name, raw[zero + 1:zero + 21].hex()
            at = zero + 21

    def ancestry_path(self, base, head):
        """Prove an original parent path, never a replace/graft/ref view.

        Every visited commit and its root tree is independently hash checked.
        No historical file blobs are needed for a parent-edge proof. Missing
        metadata is an unjudged comparison, never evidence of non-ancestry.
        """
        for identity in (base, head):
            if re.fullmatch(r"[0-9a-f]{40}", identity) is None:
                raise RuntimeError("full immutable ancestry identity required")
        pending, visited = [(head, ())], set()
        while pending:
            identity, suffix = pending.pop()
            if identity in visited:
                continue
            visited.add(identity)
            raw = self.object("commit", identity)
            # Git headers are LF-delimited. splitlines() would invent a new
            # parent edge from CR inside an otherwise malformed parent line.
            header = raw.split(b"\n\n", 1)[0].split(b"\n")
            if not header or re.fullmatch(rb"tree [0-9a-f]{40}", header[0]) is None:
                raise RuntimeError("immutable ancestry commit has no canonical tree")
            self.object("tree", header[0][5:].decode("ascii"))
            path = (identity, *suffix)
            if identity == base:
                return list(path)
            parents, at = [], 1
            while at < len(header) and header[at].startswith(b"parent "):
                if re.fullmatch(rb"parent [0-9a-f]{40}", header[at]) is None:
                    raise RuntimeError("malformed immutable parent identity")
                parents.append(header[at][7:].decode("ascii"));at += 1
            if any(line.startswith((b"parent ", b"tree ")) for line in header[at:]):
                raise RuntimeError("noncanonical immutable ancestry headers")
            pending.extend((parent, path) for parent in reversed(parents))
        raise RuntimeError("selected revision does not advance on authenticated public main")

    def verify_selected_tree(self):
        """Check all selected tree/blob bytes without materializing a checkout.

        This is the selected source closure, not full historical blob closure.
        The existing exact-object check is streamed through one Git batch
        reader so large source trees do not spawn one process per file.
        """
        process = subprocess.Popen(
            ["git", "--git-dir", str(self.directory), "cat-file", "--batch"],
            env=environment(), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL)
        seen, trees, blobs, total = set(), 0, 0, 0

        def read(kind, identity):
            process.stdin.write(identity.encode("ascii") + b"\n")
            process.stdin.flush()
            fields = process.stdout.readline().rstrip(b"\n").split(b" ")
            if len(fields) != 3 or fields[:2] != [identity.encode("ascii"), kind.encode("ascii")] \
                    or not fields[2].isdigit():
                raise RuntimeError(f"selected Git object unavailable; not judged: {identity}")
            size = int(fields[2]);remaining = size
            digest = hashlib.sha1(f"{kind} {size}\0".encode("ascii"))
            chunks = []
            while remaining:
                chunk = process.stdout.read(min(remaining, 1024 * 1024))
                if not chunk:
                    raise RuntimeError("truncated selected Git object; not judged")
                digest.update(chunk);remaining -= len(chunk)
                if kind == "tree":chunks.append(chunk)
            if process.stdout.read(1) != b"\n" or digest.hexdigest() != identity:
                raise RuntimeError("selected Git object bytes differ from Git identity")
            return b"".join(chunks), size

        try:
            pending = [("tree", self.tree)]
            while pending:
                kind, identity = pending.pop()
                if (kind, identity) in seen:
                    continue
                seen.add((kind, identity))
                raw, size = read(kind, identity);total += size
                if kind == "blob":
                    blobs += 1
                    continue
                trees += 1
                for mode, _, child in self.tree_entries(raw):
                    if mode == b"40000":pending.append(("tree", child))
                    elif mode in {b"100644", b"100755", b"120000"}:pending.append(("blob", child))
                    else:raise RuntimeError("unsupported selected source entry mode")
            process.stdin.close()
            if process.wait() != 0:
                raise RuntimeError("selected Git source reader failed; not judged")
        finally:
            if process.poll() is None:
                process.kill()
            process.wait()
            process.stdout.close()
            if not process.stdin.closed:process.stdin.close()
        return dict(tree=self.tree, trees=trees, blobs=blobs, object_bytes=total)

    def object(self, kind, identity):
        try:
            value = subprocess.check_output(
                ["git", "--git-dir", str(self.directory), "cat-file", kind, identity], env=environment(),
                stderr=subprocess.PIPE)
        except subprocess.CalledProcessError as error:
            raise RuntimeError(f"exact Git object unavailable; not judged: {identity}") from error
        header = f"{kind} {len(value)}\0".encode("ascii")
        if hashlib.sha1(header + value).hexdigest() != identity:
            raise RuntimeError(f"IR {kind} bytes differ from requested Git identity")
        return value

    def optional(self, path):
        if not isinstance(path, str) or re.fullmatch(r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*", path) is None \
                or any(part in {".", ".."} for part in path.split("/")):
            raise RuntimeError("unsafe immutable IR path")
        tree = self.tree
        parts = path.encode("ascii").split(b"/")
        for index, part in enumerate(parts):
            raw = self.object("tree", tree)
            matches = [(mode, identity) for mode, name, identity in self.tree_entries(raw) if name == part]
            if not matches:
                return None
            if len(matches) != 1:
                raise RuntimeError("ambiguous immutable IR path")
            mode, identity = matches[0]
            if index + 1 == len(parts):
                if mode not in {b"100644", b"100755"}:
                    raise RuntimeError("immutable IR input is not a regular blob")
                return self.object("blob", identity)
            if mode != b"40000":
                raise RuntimeError("non-tree ancestor of immutable IR input")
            tree = identity
        raise RuntimeError("empty immutable IR path")

    def read(self, path):
        if Path(path).name == "Cargo.toml":
            alternate = str(Path(path).with_name("Targo.toml"))
            if self.optional(alternate) is not None:
                raise RuntimeError("unsupported immutable Targo manifest precedence")
        value = self.optional(path)
        if value is None:
            raise RuntimeError(f"missing immutable IR input: {path}")
        return value
