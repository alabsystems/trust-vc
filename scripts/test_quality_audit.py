#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("quality_audit.py")
SPEC = importlib.util.spec_from_file_location("quality_audit", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
quality_audit = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = quality_audit
SPEC.loader.exec_module(quality_audit)

A = "a" * 40
C = "c" * 40
G = "d" * 40
I = "e" * 40
T = "f" * 40
DEFAULT_MANIFEST = (
    "[workspace]\n"
    "[workspace.dependencies]\n"
    f'ay-core = {{ version = "0.1.0", git = "https://github.com/alabsystems/ay.git", rev = "{A}" }}\n'
    f'tla-core = {{ git = "https://github.com/alabsystems/ty.git", rev = "{T}" }}\n'
    f'trust-ir = {{ git = "https://github.com/alabsystems/trust-ir.git", rev = "{I}" }}\n'
)


def git_source(repo: str, revision: str, resolved: str | None = None) -> str:
    resolved = resolved or revision
    return f'git+https://github.com/alabsystems/{repo}.git?rev={revision}#{resolved}'


def package(name: str, source: str | None, version: str = "0.1.0") -> str:
    source_line = f'\nsource = "{source}"' if source is not None else ""
    return f'[[package]]\nname = "{name}"\nversion = "{version}"{source_line}\n'


class FirstPartyLockAuditTests(unittest.TestCase):
    def audit(self, packages: list[str], manifest: str = DEFAULT_MANIFEST) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            root.joinpath("Cargo.toml").write_text(manifest, encoding="utf-8")
            root.joinpath("Cargo.lock").write_text(
                "version = 4\n\n" + "\n".join(packages), encoding="utf-8"
            )
            return [finding.message for finding in quality_audit.audit_first_party_lock(root)]

    def test_coherent_graph_accepts_ay_path_plus_same_rev_git(self) -> None:
        messages = self.audit(
            [
                package("ay-core", None),
                package("ay-proof", git_source("ay", A)),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertEqual(messages, [])

    def test_split_and_stale_authorities_fail_closed(self) -> None:
        old = "b" * 40
        messages = self.audit(
            [
                package("ay-core", None),
                package("ay-proof", git_source("ay", A)),
                package("ay-sat", git_source("ay", old)),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", old)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertTrue(
            any("ay packages must resolve from one exact Git rev" in item for item in messages)
        )
        self.assertTrue(any("trust-ir lock rev" in item for item in messages))

    def test_source_query_and_resolved_commit_must_agree(self) -> None:
        old = "b" * 40
        messages = self.audit(
            [
                package("ay-core", git_source("ay", A, old)),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertTrue(
            any("requested rev" in item and "resolves as" in item for item in messages)
        )

    def test_path_only_ay_is_accepted_by_lock_coherence_audit(self) -> None:
        messages = self.audit(
            [
                package("ay-core", None),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertEqual(messages, [])

    def test_manifest_direct_pin_must_be_full_and_use_expected_repo(self) -> None:
        short = "a" * 12
        manifest = DEFAULT_MANIFEST.replace(A, short).replace(
            "https://github.com/alabsystems/trust-ir.git",
            "https://example.invalid/trust-ir.git",
        )
        messages = self.audit(
            [
                package("ay-core", git_source("ay", A)),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ],
            manifest,
        )
        self.assertTrue(any("40 lowercase hex" in item for item in messages))
        self.assertTrue(
            any("trust-ir does not use the expected trust-ir" in item for item in messages)
        )

    def test_first_party_package_from_unrecognized_source_fails_closed(self) -> None:
        messages = self.audit(
            [
                package("ay-core", "registry+https://github.com/rust-lang/crates.io-index"),
                package("ay-proof", git_source("ay", A)),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertTrue(
            any("ay-core does not resolve from the expected ay" in item for item in messages)
        )

    def test_missing_transitive_authority_fails_closed(self) -> None:
        messages = self.audit(
            [
                package("ay-core", git_source("ay", A)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertTrue(
            any("clean packages must resolve" in item for item in messages)
        )

    def test_a_lock_without_ty_or_trust_cg_is_coherent(self) -> None:
        manifest = "\n".join(
            line for line in DEFAULT_MANIFEST.splitlines() if not line.startswith("tla-core")
        ) + "\n"
        messages = self.audit(
            [
                package("ay-core", None),
                package("clean-kernel", git_source("clean", C)),
                package("trust-ir", git_source("trust-ir", I)),
            ],
            manifest,
        )
        self.assertEqual(messages, [])
        # Present, a ty package still needs one exact rev.
        split = self.audit(
            [
                package("ay-core", None),
                package("clean-kernel", git_source("clean", C)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
                package("tla-check", git_source("ty", A)),
            ],
            manifest,
        )
        self.assertTrue(any("ty packages must resolve" in item for item in split), split)

    def test_duplicate_rev_query_is_not_an_exact_lock_authority(self) -> None:
        duplicated = (
            "git+https://github.com/alabsystems/ay.git"
            f"?rev={A}&rev={'b' * 40}#{A}"
        )
        messages = self.audit(
            [
                package("ay-core", duplicated),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertTrue(any("has no single exact ay ?rev" in item for item in messages))

    def test_ay_manifest_version_must_match_path_lock_version(self) -> None:
        messages = self.audit(
            [
                package("ay-core", None, "0.2.0"),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertTrue(
            any(
                "ay lock version 0.2.0 does not match manifest version 0.1.0"
                in item
                for item in messages
            )
        )

    def test_split_ay_manifest_and_lock_versions_fail_closed(self) -> None:
        split_manifest = DEFAULT_MANIFEST.replace(
            f'ay-core = {{ version = "0.1.0", git = "https://github.com/alabsystems/ay.git", rev = "{A}" }}',
            (
                f'ay-core = {{ version = "0.1.0", git = "https://github.com/alabsystems/ay.git", rev = "{A}" }}\n'
                f'ay-sys = {{ version = "0.2.0", git = "https://github.com/alabsystems/ay.git", rev = "{A}" }}'
            ),
        )
        messages = self.audit(
            [
                package("ay-core", None, "0.1.0"),
                package("ay-sys", None, "0.2.0"),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ],
            split_manifest,
        )
        self.assertTrue(
            any(
                "ay direct dependencies must share one exact package version" in item
                for item in messages
            )
        )
        self.assertTrue(
            any("ay packages must resolve at one package version" in item for item in messages)
        )

    def test_ay_manifest_requires_exact_version(self) -> None:
        manifest = DEFAULT_MANIFEST.replace('version = "0.1.0", ', "")
        messages = self.audit(
            [
                package("ay-core", None),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ],
            manifest,
        )
        self.assertTrue(any("must carry AY's exact package version" in item for item in messages))

    def test_noncanonical_first_party_git_authority_fails_closed(self) -> None:
        extra_query = (
            "git+https://github.com/alabsystems/ay.git"
            f"?rev={A}&branch=main#{A}"
        )
        messages = self.audit(
            [
                package("ay-core", extra_query),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertTrue(any("has no single exact ay ?rev" in item for item in messages))

        insecure_manifest = DEFAULT_MANIFEST.replace(
            "https://github.com/alabsystems/ay.git",
            "http://github.com/alabsystems/ay.git",
        )
        messages = self.audit(
            [
                package("ay-core", None),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ],
            insecure_manifest,
        )
        self.assertTrue(any("does not use the expected ay" in item for item in messages))

    def test_noncanonical_owned_source_cannot_hide_behind_package_name(self) -> None:
        renamed_package_source = (
            "git+ssh://git@github.com/alabsystems/ay.git"
            f"?rev={A}#{A}"
        )
        messages = self.audit(
            [
                package("ay-core", None),
                package("renamed-solver", renamed_package_source),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ]
        )
        self.assertTrue(
            any("renamed-solver has noncanonical ay Git authority" in item for item in messages)
        )

    def test_package_version_is_complete_semver(self) -> None:
        malformed_manifest = DEFAULT_MANIFEST.replace("0.1.0", "0.1.0-alpha..1")
        messages = self.audit(
            [
                package("ay-core", None),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ],
            malformed_manifest,
        )
        self.assertTrue(any("one complete Cargo package version" in item for item in messages))

        prerelease_manifest = DEFAULT_MANIFEST.replace(
            "0.1.0", "0.1.0-alpha.1+build.5"
        )
        messages = self.audit(
            [
                package("ay-core", None, "0.1.0-alpha.1+build.5"),
                package("clean-kernel", git_source("clean", C)),
                package("trust-cg-ir", git_source("trust-cg", G)),
                package("trust-ir", git_source("trust-ir", I)),
                package("tla-core", git_source("ty", T)),
            ],
            prerelease_manifest,
        )
        self.assertEqual(messages, [])


if __name__ == "__main__":
    unittest.main()
