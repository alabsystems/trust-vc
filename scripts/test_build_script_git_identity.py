#!/usr/bin/env python3
"""Compile the real build script in clean Git probes with genuine Targo.

Run through build-slot with TARGO and RUSTC naming the selected Trust tools.
The probes have no dependencies and claim only their own fixture Git identity.
Set TVC_BUILD_SCRIPT_TEST_DIR to retain fixtures for diagnostic evidence.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest

SOURCE = Path(__file__).resolve().parents[1] / "crates/trust-vc-core/build.rs"


class BuildScriptGitIdentity(unittest.TestCase):
    def setUp(self):
        self.targo = Path(os.environ["TARGO"]).resolve(strict=True)
        self.rustc = Path(os.environ["RUSTC"]).resolve(strict=True)
        retained = os.environ.get("TVC_BUILD_SCRIPT_TEST_DIR")
        if retained is None:
            temporary = tempfile.TemporaryDirectory(prefix=self._testMethodName + "-")
            self.addCleanup(temporary.cleanup)
            self.directory = Path(temporary.name)
        else:
            self.directory = Path(tempfile.mkdtemp(
                prefix=self._testMethodName + "-", dir=retained,
            ))
        self.repo = self.directory / "repo"
        self.repo.mkdir()
        self.serial = 0
        self.env = {
            "PATH": str(self.rustc.parent) + os.pathsep + "/usr/bin:/bin:/usr/sbin:/sbin",
            "HOME": str(self.directory / "home"),
            "CARGO_HOME": str(self.directory / "cargo-home"),
            "TMPDIR": str(self.directory / "tmp"),
            "RUSTC": str(self.rustc),
            "CARGO_BUILD_JOBS": os.environ.get("CARGO_BUILD_JOBS", "1"),
            "CARGO_NET_OFFLINE": "true",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_AUTHOR_NAME": "Build script probe",
            "GIT_AUTHOR_EMAIL": "probe@local.invalid",
            "GIT_COMMITTER_NAME": "Build script probe",
            "GIT_COMMITTER_EMAIL": "probe@local.invalid",
        }
        for key in ("HOME", "CARGO_HOME", "TMPDIR"):
            Path(self.env[key]).mkdir(mode=0o700)
        self.command([self.targo, "--unverified", "--version"])
        (self.repo / "crates/trust-vc-core").mkdir(parents=True)
        (self.repo / "src").mkdir()
        (self.repo / "crates/trust-vc-core/build.rs").write_bytes(SOURCE.read_bytes())
        (self.repo / "Cargo.toml").write_text(
            '[package]\nname="vc_ref_identity_probe"\nversion="0.0.0"\n'
            'edition="2024"\nbuild="crates/trust-vc-core/build.rs"\n[workspace]\n'
        )
        (self.repo / "src/main.rs").write_text(
            'fn main() { println!("identity={}", env!("TVC_CORE_BUILD_GIT_HEAD")); }\n'
        )
        self.command([self.targo, "generate-lockfile", "--offline"])
        self.git("init")
        self.git("add", ".")
        self.git("commit", "-m", "Track exact build script and identity probe")
        self.initial = self.git("rev-parse", "HEAD").stdout.strip()
        tree = self.git("rev-parse", "HEAD^{tree}").stdout.strip()
        self.successor = self.git(
            "commit-tree", tree, "-p", self.initial, "-m", "Same-tree successor"
        ).stdout.strip()

    def command(self, argv, *, repo=None):
        result = subprocess.run(
            [str(arg) for arg in argv], cwd=repo or self.repo, env=self.env,
            capture_output=True, text=True, timeout=180,
        )
        self.serial += 1
        stem = self.directory / f"command-{self.serial:03}"
        stem.with_suffix(".stdout").write_text(result.stdout)
        stem.with_suffix(".stderr").write_text(result.stderr)
        stem.with_suffix(".json").write_text(json.dumps({
            "argv": [str(arg) for arg in argv], "cwd": str(repo or self.repo),
            "exit_code": result.returncode,
        }, indent=2) + "\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def git(self, *args):
        return self.command(["/usr/bin/git", *args])

    def build(self, expected, *, fresh=False):
        result = self.command([
            self.targo, "--unverified", "run", "--locked", "--offline", "-vv",
            "--target-dir", self.directory / "target",
        ])
        self.assertEqual(
            [line for line in result.stdout.splitlines() if line.startswith("identity=")],
            ["identity=" + expected], result.stdout + result.stderr,
        )
        if fresh:
            self.assertIn("Fresh vc_ref_identity_probe", result.stderr)
            self.assertNotIn("Dirty vc_ref_identity_probe", result.stderr)

    def stable_git_inputs(self):
        return {
            name: (hashlib.sha256((self.repo / ".git" / name).read_bytes()).hexdigest(),
                   (self.repo / ".git" / name).stat().st_mtime_ns)
            for name in ("HEAD", "index", "packed-refs")
        }

    def test_packed_nested_creation_deletion_and_repack(self):
        ref = "refs/heads/topic/subtopic/deep"
        self.git("switch", "-c", "topic/subtopic/deep")
        self.git("pack-refs", "--all", "--prune")
        self.git("update-ref", "refs/heads/anchor", self.initial)
        self.assertFalse((self.repo / ".git/refs/heads/topic").exists())
        self.build(self.initial)
        self.build(self.initial, fresh=True)
        before = self.stable_git_inputs()
        time.sleep(1.1)  # Ensure the actual ref mutation follows Cargo's last run.
        self.git("update-ref", ref, self.successor, self.initial)
        self.assertEqual(self.git("status", "--porcelain=v1").stdout, "")
        self.assertEqual(before, self.stable_git_inputs())
        self.build(self.successor)
        self.build(self.successor, fresh=True)
        self.git("pack-refs", "--all", "--prune")
        self.build(self.successor)
        self.build(self.successor, fresh=True)
        self.git("update-ref", "-d", ref, self.successor)
        self.build("")  # Unborn/missing HEAD must not authenticate a cache.
        self.build("", fresh=True)
        self.git("update-ref", ref, self.initial)
        self.build(self.initial)
        self.build(self.initial, fresh=True)

    def test_missing_heads_directory_watches_refs_root(self):
        self.git("switch", "-c", "missing/topic")
        self.git("pack-refs", "--all", "--prune")
        heads = self.repo / ".git/refs/heads"
        if heads.exists():
            heads.rmdir()  # All branch refs were packed; remove only this empty directory.
        self.assertFalse(heads.exists())
        self.assertTrue((self.repo / ".git/refs").is_dir())
        self.build(self.initial)
        self.build(self.initial, fresh=True)
        time.sleep(1.1)
        self.git("update-ref", "refs/heads/missing/topic", self.successor, self.initial)
        self.build(self.successor)
        self.build(self.successor, fresh=True)
        self.git("config", "probe.unrelated", "true")
        self.build(self.successor, fresh=True)

    def test_detached_loose_and_unrelated_git_metadata(self):
        self.git("switch", "-c", "ordinary")
        self.build(self.initial)
        self.build(self.initial, fresh=True)
        self.git("update-ref", "refs/heads/ordinary", self.successor, self.initial)
        self.build(self.successor)
        self.build(self.successor, fresh=True)
        self.git("switch", "--detach", self.initial)
        self.build(self.initial)
        self.build(self.initial, fresh=True)
        before = (self.repo / ".git/index").read_bytes()
        self.git("config", "probe.unrelated", "true")
        self.build(self.initial, fresh=True)
        self.assertEqual(before, (self.repo / ".git/index").read_bytes())

    def test_dirty_source_and_forged_environment_cannot_authenticate(self):
        self.build(self.initial)
        source = self.repo / "crates/trust-vc-core/untracked.rs"
        source.write_text("// untracked source must disable cache identity\n")
        self.env["TVC_CORE_BUILD_GIT_HEAD"] = "a" * 40
        self.build("")
        source.unlink()
        self.build(self.initial)
        self.build(self.initial, fresh=True)

    def test_linked_worktree_packed_nested_ref(self):
        self.git("branch", "linked/topic/deep")
        self.git("pack-refs", "--all", "--prune")
        linked = self.directory / "linked"
        self.git("worktree", "add", str(linked), "linked/topic/deep")
        self.repo = linked
        self.assertTrue((linked / ".git").is_file())
        self.build(self.initial)
        self.build(self.initial, fresh=True)
        time.sleep(1.1)
        self.git("update-ref", "refs/heads/linked/topic/deep", self.successor, self.initial)
        self.build(self.successor)
        self.build(self.successor, fresh=True)


if __name__ == "__main__":
    unittest.main()
