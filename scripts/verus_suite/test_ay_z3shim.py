#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Offline tests for the measurement shim (ay_z3shim.py), driven by a fake solver.

What is pinned here, and why:
  * the shim never reads stdin through sys.stdin. A thread blocked in
    sys.stdin.buffer.readline made Python 3.9 abort at exit (SIGABRT, "Fatal Python
    error: _enter_buffered_busy", one macOS crash report per solver process), so the
    stdin thread reads fd 0 with os.read. StdinSourceTest checks that on the SOURCE,
    with ast, without running it: a regression is caught before any process can abort.
    No test here runs a shim that reads stdin through sys.stdin;
  * stdin_lines() splits a pipe exactly as io.BufferedReader.readline does; the
    replacement must not change a byte;
  * every way the shim can end (normal close, the solver exiting while AIR still holds
    stdin open, the wall kill, the CPU kill, SIGINT) ends cleanly: no SIGABRT, no
    "Fatal Python error" or "Exception in thread" on the stderr AIR shares with the
    Verus harness;
  * Transcript drops a write that comes after close instead of raising, and a close
    racing concurrent writes raises nothing: TranscriptTest checks that in-process,
    deterministically (the subprocess race below almost never reaches that branch,
    because AIR's side of the pipe breaks first), and the end-to-end race (the solver
    answers and exits while AIR keeps writing) still ends cleanly over many repetitions;
  * AY_BIN has no default: unset, the shim refuses with a clear message;
  * AY_SHIM_ARGS defaults to "-q --z3-mode" (ay's z3 mode, the only mode AIR accepts);
  * the end-state defaults (stderr forwarded AND recorded; :rlimit-count forwarded
    unchanged) and the two opt-outs that restore the recorded runs' behaviour, with
    the recorded event-log keys, in order.
With VERUS_BASELINE_ROOT pointing at a recorded run tree that still holds the shims
the 2026-09-23 runs used (bin/ay-z3shim, bin/ay-z3shim-cpu), the opt-out mode is also
compared with them byte for byte; otherwise that test is skipped.
"""
from __future__ import annotations

import ast
import hashlib
import importlib.util
import json
import os
import random
import shlex
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
SHIM = HERE / "ay_z3shim.py"

FAKE_SOLVER = r'''
import os, select, sys
mode = os.environ.get("FAKE_MODE", "unsat")
counts = [int(x) for x in os.environ.get("FAKE_RLIMIT", "10").split(",")]
n_stat = 0
def say(s):
    sys.stdout.write(s + "\n")
    sys.stdout.flush()
if os.environ.get("FAKE_STDERR"):
    sys.stderr.write(os.environ["FAKE_STDERR"] + "\n")
    sys.stderr.flush()
for raw in iter(sys.stdin.buffer.readline, b""):
    line = raw.decode(errors="replace").strip()
    if line == "(check-sat)":
        if mode == "exit-now":
            say("unknown")
            sys.stderr.write('(error "unsupported logic: fake refusal")\n')
            sys.stderr.flush()
            sys.exit(1)
        if mode == "exit-after-answer":
            say("unsat")
            sys.exit(0)
        if mode == "hang":
            while os.read(0, 1 << 16):
                pass
            sys.exit(0)
        if mode == "spin":
            while True:
                x = 0
                for i in range(100000):
                    x += i
                if select.select([0], [], [], 0)[0] and not os.read(0, 1 << 16):
                    sys.exit(0)
        say(mode)
    elif line.startswith("(echo"):
        say(line[len('(echo "'):-2])
    elif line == "(get-info :reason-unknown)":
        say('(:reason-unknown "(incomplete quantifiers)")')
    elif line == "(get-info :all-statistics)":
        say("(:rlimit-count %d :time 0.00)" % counts[min(n_stat, len(counts) - 1)])
        n_stat += 1
sys.exit(int(os.environ.get("FAKE_EOF_RC", "0")))
'''

LINE_READER = r'''
import importlib.util, io, os, sys
mode = sys.argv[2]
if mode == "buffered":
    reader = io.BufferedReader(io.FileIO(0, "rb", closefd=False))
    lines = iter(reader.readline, b"")
else:
    spec = importlib.util.spec_from_file_location("ay_z3shim", sys.argv[1])
    shim = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(shim)
    if mode == "shim-nonblocking":
        os.set_blocking(0, False)   # exercises the BlockingIOError -> select branch
    lines = shim.stdin_lines()
out = io.FileIO(1, "wb", closefd=False)
for line in lines:
    out.write(len(line).to_bytes(8, "big") + line)
'''

# The event-log keys of the shims behind the recorded 2026-09-23 runs, in order.
RECORDED_KEYS = ["test", "pid", "solver", "argv", "start", "wall_s", "rc", "killed", "after_kill",
                 "pending_at_exit", "answers", "unanswered_prefix", "reason_unknown", "errors",
                 "stdin_bytes", "stderr_tail"]
RECORDED_CPU_KEYS = RECORDED_KEYS[:8] + ["kill_cpu_s", "kill_pending_s", "kill_loadavg"] + RECORDED_KEYS[8:]

BAD_STDERR = ("Fatal Python error", "Exception in thread")
SESSION = (b"(set-option :rlimit 30000000)\n(push)\n(declare-const x Int)\n(assert (> x 0))\n"
           b"(check-sat)\n(set-option :rlimit 0)\n(echo \"<<DONE>>\")\n(get-info :reason-unknown)\n"
           b"(get-info :all-statistics)\n(pop)\n(push)\n(check-sat)\n(echo \"<<DONE>>\")\n"
           b"(get-info :all-statistics)\n(pop)\n")


def load_shim(path=SHIM, name="ay_z3shim_under_test"):
    """Import the shim as a module. main() is guarded, so nothing runs: only its
    definitions and module-level state are created."""
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reference_lines(data: bytes) -> list[bytes]:
    """Split after every b"\\n"; an unterminated tail is the last line."""
    out, start = [], 0
    while True:
        nl = data.find(b"\n", start)
        if nl < 0:
            break
        out.append(data[start:nl + 1])
        start = nl + 1
    if start < len(data):
        out.append(data[start:])
    return out


def prefix_hashes(stream: bytes) -> list[str]:
    h, out = hashlib.sha256(), []
    for line in reference_lines(stream):
        h.update(line)
        if line.strip() == b"(check-sat)":
            out.append(h.hexdigest()[:20])
    return out


class ShimCase(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="verus-suite-shim-")
        self.tmp = Path(self._tmp.name)
        self.fake = self.tmp / "fake-solver"
        source = self.tmp / "fake_solver.py"
        source.write_text(FAKE_SOLVER)
        # A shebang splits an interpreter path at whitespace. Keep the actual
        # selected Python even when its installation directory contains spaces.
        self.fake.write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable) + " "
                             + shlex.quote(str(source)) + ' "$@"\n')
        self.fake.chmod(0o755)
        self.events = self.tmp / "events"

    def tearDown(self):
        self._tmp.cleanup()

    def env(self, **extra):
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("AY_", "SHIM_", "FAKE_", "TOP3_"))}
        env.update(AY_BIN=str(self.fake), AY_SHIM_ARGS="-q --z3-mode", AY_SHIM_EVENT_DIR=str(self.events))
        env.update({k: v for k, v in extra.items() if v is not None})
        for k in [k for k, v in extra.items() if v is None]:
            env.pop(k, None)
        return env

    def start(self, shim=SHIM, **extra):
        return subprocess.Popen([sys.executable, str(shim), "-smt2", "-in"], stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=self.env(**extra),
                                start_new_session=True)

    def finish(self, p, timeout=30):
        if p.stdin is not None and p.stdin.closed:
            p.stdin = None  # Python 3.9's communicate() flushes stdin even when it is closed
        try:
            out, err = p.communicate(timeout=timeout)
        finally:
            try:
                os.killpg(p.pid, signal.SIGKILL)  # the fake solver, should anything be left
            except (ProcessLookupError, PermissionError):
                pass
        return p.returncode, out, err.decode(errors="replace")

    def events_logged(self, directory=None):
        d = directory or self.events
        return [json.loads(line) for f in sorted(Path(d).glob("*.jsonl"))
                for line in f.read_text().splitlines() if line.strip()]

    def assert_clean_exit(self, rc, err):
        self.assertNotEqual(rc, -signal.SIGABRT, err)
        for bad in BAD_STDERR:
            self.assertNotIn(bad, err)

    def hold_open_until_exit(self, p, timeout=30):
        """Write nothing more, keep stdin open, and wait for the shim to end."""
        t0 = time.time()
        while p.poll() is None and time.time() - t0 < timeout:
            time.sleep(0.05)
        self.assertIsNotNone(p.poll(), "the shim did not exit")
        return self.finish(p)


class StdinLinesTest(unittest.TestCase):
    """(a) stdin_lines() over a real pipe equals io.BufferedReader.readline."""

    def streams(self):
        rng = random.Random(20260924)
        pieces = [b"\n", b"\r", b"\r\n", b"\0", b"(check-sat)\n", b"(echo \"<<DONE>>\")\n", b"x" * 7,
                  bytes(range(256)), b"\n\n\n"]
        fixed = [b"", b"\n", b"no trailing newline", b"a\nb", b"\r\r\r", b"\0\0\n\0",
                 b"L" * (70 * 1024) + b"\n" + b"M" * (200 * 1024),          # lines > 64 KiB
                 (b"y" * 65535 + b"\n") * 3 + b"z" * 65536,                   # around the read size
                 b"\n" * 5000]
        out = list(fixed)
        for _ in range(12):
            parts = []
            for _ in range(rng.randint(1, 400)):
                if rng.random() < 0.02:
                    parts.append(os.urandom(rng.randint(60 * 1024, 140 * 1024)).replace(b"\n", b"_"))
                elif rng.random() < 0.5:
                    parts.append(rng.choice(pieces))
                else:
                    parts.append(os.urandom(rng.randint(0, 300)))
            data = b"".join(parts)
            if rng.random() < 0.5:
                data = data.rstrip(b"\n")
            out.append(data)
        return rng, out

    def read_through_pipe(self, program, mode, data, rng):
        p = subprocess.Popen([sys.executable, str(program), str(SHIM), mode], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        chunks = []
        i = 0
        while i < len(data):
            n = rng.choice([1, 2, 3, 17, 4096, 65535, 65536, 65537, 150000])
            chunks.append(data[i:i + n])
            i += n
        # the rng is shared, so draw every choice before the writer thread starts
        pauses = [rng.random() < 0.05 for _ in chunks]

        def writer():
            try:
                for c, pause in zip(chunks, pauses):
                    p.stdin.write(c)
                    p.stdin.flush()
                    if pause:
                        time.sleep(0.001)   # let the reader see a partial line
            finally:
                p.stdin.close()

        t = threading.Thread(target=writer)
        t.start()
        with p.stdout, p.stderr:
            out = p.stdout.read()
            err = p.stderr.read()
        t.join()
        p.wait()
        self.assertEqual(p.returncode, 0, err.decode(errors="replace"))
        lines, j = [], 0
        while j < len(out):
            n = int.from_bytes(out[j:j + 8], "big")
            lines.append(out[j + 8:j + 8 + n])
            j += 8 + n
        return lines

    def test_stdin_lines_matches_buffered_readline(self):
        with tempfile.TemporaryDirectory(prefix="verus-suite-lines-") as tmp:
            program = Path(tmp) / "line_reader.py"
            program.write_text(LINE_READER)
            rng, streams = self.streams()
            for k, data in enumerate(streams):
                with self.subTest(stream=k, size=len(data)):
                    want = reference_lines(data)
                    buffered = self.read_through_pipe(program, "buffered", data, rng)
                    shim = self.read_through_pipe(program, "shim", data, rng)
                    nonblocking = self.read_through_pipe(program, "shim-nonblocking", data, rng)
                    self.assertEqual(buffered, want)
                    self.assertEqual(shim, buffered)
                    self.assertEqual(nonblocking, buffered)


FD0_WRAPPERS = {"open", "io.open", "os.fdopen", "io.FileIO", "io.BufferedReader", "io.TextIOWrapper"}


def stdin_problems(source: str) -> list[str]:
    """Every way `source` reads stdin other than os.read on fd 0, found by parsing it (the
    code is never run). Docstrings and comments are not code, so they may name sys.stdin."""
    tree = ast.parse(source)
    problems = []
    for node in ast.walk(tree):
        if (isinstance(node, ast.Attribute) and node.attr in ("stdin", "__stdin__")
                and isinstance(node.value, ast.Name) and node.value.id == "sys"):
            problems.append(f"line {node.lineno}: sys.{node.attr}")
        elif isinstance(node, ast.ImportFrom) and node.module == "sys" and any(
                a.name in ("stdin", "__stdin__") for a in node.names):
            problems.append(f"line {node.lineno}: from sys import stdin")
        elif isinstance(node, ast.Call):
            func = ast.unparse(node.func)
            if func == "input":
                problems.append(f"line {node.lineno}: input()")
            elif (func in FD0_WRAPPERS and node.args and isinstance(node.args[0], ast.Constant)
                  and node.args[0].value == 0):
                problems.append(f"line {node.lineno}: {func}(0, ...) wraps fd 0 in a locking reader")
    functions = {n.name: n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)}
    reader = functions.get("stdin_lines")
    if reader is None:
        problems.append("no stdin_lines()")
    elif not any(isinstance(n, ast.Call) and ast.unparse(n.func) == "os.read" and n.args
                 and isinstance(n.args[0], ast.Constant) and n.args[0].value == 0
                 for n in ast.walk(reader)):
        problems.append("stdin_lines() does not call os.read(0, ...)")
    pump = functions.get("pump_stdin")
    if pump is None or not any(isinstance(n, ast.Call) and ast.unparse(n.func) == "stdin_lines"
                               for n in ast.walk(pump)):
        problems.append("pump_stdin() does not read through stdin_lines()")
    return problems


class StdinSourceTest(unittest.TestCase):
    """The stdin reader never goes back to sys.stdin. Checked on the source text with ast,
    never by running a shim that reads stdin that way: such a shim aborts with SIGABRT at
    exit and files a macOS crash report."""

    def test_the_shim_reads_fd_0_with_os_read_only(self):
        self.assertEqual(stdin_problems(SHIM.read_text()), [])

    def test_the_check_catches_a_buffered_reader(self):
        # The regression, spliced into the real source as TEXT. Nothing here executes it.
        source = SHIM.read_text()
        for replacement in ("sys.stdin.buffer.read1(1 << 16)", "sys.stdin.buffer.readline()",
                            "open(0, 'rb').read1(1 << 16)"):
            with self.subTest(replacement=replacement):
                mutated = source.replace("os.read(0, 1 << 16)", replacement)
                self.assertNotEqual(mutated, source, "the splice point is gone from the shim")
                problems = stdin_problems(mutated)
                self.assertTrue(any("os.read(0" in p for p in problems), problems)
                self.assertTrue(any("sys.stdin" in p or "fd 0" in p for p in problems), problems)
        mutated = source.replace("for line in stdin_lines():", "for line in iter(sys.stdin.buffer.readline, b''):")
        self.assertNotEqual(mutated, source)
        self.assertTrue(stdin_problems(mutated))


class TranscriptTest(unittest.TestCase):
    """(c) Transcript, in-process: a write after close is dropped, never raised, and a
    close racing concurrent writes raises nothing and never tears a write."""

    def setUp(self):
        self.shim = load_shim()
        self._tmp = tempfile.TemporaryDirectory(prefix="verus-suite-transcript-")
        self.path = Path(self._tmp.name) / "t.out"

    def tearDown(self):
        self._tmp.cleanup()

    def test_write_after_close_is_dropped(self):
        t = self.shim.Transcript(str(self.path))
        t.write(b"a\n")
        t.close()
        t.write(b"late\n")
        t.close()
        self.assertEqual(self.path.read_bytes(), b"a\n")
        self.assertEqual(self.shim.transcript_errors, [])

    def test_close_racing_writers(self):
        interval = sys.getswitchinterval()
        sys.setswitchinterval(1e-6)  # switch threads as often as the interpreter can
        self.addCleanup(sys.setswitchinterval, interval)
        for rep in range(40):
            with self.subTest(rep=rep):
                t = self.shim.Transcript(str(self.path))
                errors = []
                start = threading.Barrier(5)

                def writer(k):
                    start.wait()
                    try:
                        for i in range(1500):
                            t.write(b"%d:%d\n" % (k, i))
                    except BaseException as e:  # noqa: BLE001 - any exception is the failure
                        errors.append(f"writer {k}: {e!r}")

                def closer():
                    start.wait()
                    time.sleep(0.0005 * (rep % 8))
                    try:
                        t.close()
                    except BaseException as e:  # noqa: BLE001
                        errors.append(f"closer: {e!r}")

                threads = [threading.Thread(target=writer, args=(k,)) for k in range(4)]
                threads.append(threading.Thread(target=closer))
                for th in threads:
                    th.start()
                for th in threads:
                    th.join()
                t.write(b"after\n")  # the transcript is closed by now
                self.assertEqual(errors, [])
                self.assertEqual(self.shim.transcript_errors, [])
                data = self.path.read_bytes()
                self.assertTrue(data == b"" or data.endswith(b"\n"), data[-40:])
                for line in data.splitlines():
                    k, _, i = line.partition(b":")
                    self.assertTrue(k.isdigit() and i.isdigit(), line)
                self.assertNotIn(b"after", data)

    def test_open_failure_ends_the_transcript_and_is_recorded(self):
        t = self.shim.Transcript(str(Path(self._tmp.name) / "missing-dir" / "t.out"))
        t.write(b"x\n")
        t.close()
        self.assertEqual(len(self.shim.transcript_errors), 1)
        self.assertTrue(self.shim.transcript_errors[0].startswith("open "))


class ExitScenarioTest(ShimCase):
    """(b) every exit path is clean: no SIGABRT, no fatal error, no thread exception."""

    def test_normal_close(self):
        p = self.start()
        p.stdin.write(SESSION)
        p.stdin.close()
        rc, out, err = self.finish(p)
        self.assert_clean_exit(rc, err)
        self.assertEqual(rc, 0, err)
        self.assertEqual(out, b"unsat\n<<DONE>>\n(:reason-unknown \"(incomplete quantifiers)\")\n"
                              b"(:rlimit-count 10 :time 0.00)\nunsat\n<<DONE>>\n(:rlimit-count 10 :time 0.00)\n")
        (ev,) = self.events_logged()
        self.assertEqual(ev["rc"], 0)
        self.assertIsNone(ev["killed"])
        self.assertEqual([a[0] for a in ev["answers"]], ["unsat", "unsat"])
        self.assertEqual([a[2] for a in ev["answers"]], prefix_hashes(SESSION))
        self.assertEqual(ev["stdin_bytes"], len(SESSION))

    def test_solver_exits_while_stdin_is_held_open(self):
        p = self.start(FAKE_MODE="exit-now")
        p.stdin.write(b"(check-sat)\n")
        p.stdin.flush()
        rc, out, err = self.hold_open_until_exit(p)
        self.assert_clean_exit(rc, err)
        self.assertEqual(rc, 1)
        self.assertEqual(out, b"unknown\n")
        (ev,) = self.events_logged()
        self.assertEqual(ev["rc"], 1)
        self.assertIn("fake refusal", ev["stderr_tail"])

    def test_wall_kill(self):
        p = self.start(FAKE_MODE="hang", AY_SHIM_QUERY_WALL_S="1")
        p.stdin.write(b"(check-sat)\n")
        p.stdin.flush()
        rc, out, err = self.hold_open_until_exit(p)
        self.assert_clean_exit(rc, err)
        self.assertEqual(rc, 1)
        (ev,) = self.events_logged()
        self.assertEqual(ev["killed"], "check-sat unanswered after 1 s")
        self.assertEqual(ev["pending_at_exit"], 1)
        self.assertEqual(ev["unanswered_prefix"], prefix_hashes(b"(check-sat)\n"))
        self.assertNotIn("kill_cpu_s", ev)

    def test_cpu_kill(self):
        p = self.start(FAKE_MODE="spin", AY_SHIM_QUERY_CPU_S="0.5", AY_SHIM_QUERY_WALL_MAX_S="60")
        p.stdin.write(b"(check-sat)\n")
        p.stdin.flush()
        rc, out, err = self.hold_open_until_exit(p, timeout=60)
        self.assert_clean_exit(rc, err)
        (ev,) = self.events_logged()
        self.assertEqual(ev["killed"], "check-sat unanswered after 0.5 CPU s")
        self.assertGreaterEqual(ev["kill_cpu_s"], 0.5)
        self.assertIsInstance(ev["kill_pending_s"], float)
        self.assertIsInstance(ev["kill_loadavg"], float)

    def test_cpu_mode_wall_backstop(self):
        p = self.start(FAKE_MODE="hang", AY_SHIM_QUERY_CPU_S="30", AY_SHIM_QUERY_WALL_MAX_S="1")
        p.stdin.write(b"(check-sat)\n")
        p.stdin.flush()
        rc, out, err = self.hold_open_until_exit(p)
        self.assert_clean_exit(rc, err)
        (ev,) = self.events_logged()
        self.assertEqual(ev["killed"], "check-sat unanswered after 1 wall s")

    def test_sigint(self):
        p = self.start(FAKE_MODE="hang")
        p.stdin.write(b"(check-sat)\n")
        p.stdin.flush()
        time.sleep(1.0)  # let the shim reach its read loop
        p.send_signal(signal.SIGINT)
        rc, out, err = self.hold_open_until_exit(p)
        self.assert_clean_exit(rc, err)
        self.assertNotEqual(rc, 0)


class TranscriptCloseRaceTest(ShimCase):
    """End to end: the solver answers and exits while the driver keeps writing, and the
    shim still ends cleanly with whole transcripts. The write-after-close branch of
    Transcript is almost never reached this way (AIR's pipe to the solver breaks first);
    TranscriptTest pins that branch."""

    def one(self, i):
        tdir = self.tmp / f"tx{i}"
        p = subprocess.Popen([sys.executable, str(SHIM), "-smt2", "-in"], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True,
                             env=self.env(FAKE_MODE="exit-after-answer", AY_SHIM_TRANSCRIPT_DIR=str(tdir),
                                          AY_SHIM_EVENT_DIR=str(self.tmp / f"ev{i}")))
        drained = {}

        def drain(name, f):
            with f:
                drained[name] = f.read()

        readers = [threading.Thread(target=drain, args=("out", p.stdout)),
                   threading.Thread(target=drain, args=("err", p.stderr))]
        for t in readers:
            t.start()
        try:
            p.stdin.write(b"(check-sat)\n")
            p.stdin.flush()
            t0 = time.time()
            while p.poll() is None and time.time() - t0 < 20:
                p.stdin.write(b"(assert (= 1 1))\n" * 50)
                p.stdin.flush()
        except (BrokenPipeError, OSError):
            pass
        try:
            p.stdin.close()
        except (BrokenPipeError, OSError):
            pass
        p.wait(timeout=30)
        for t in readers:
            t.join(timeout=30)
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        return p.returncode, drained.get("out", b""), drained.get("err", b"").decode(errors="replace"), tdir

    def test_close_race(self):
        with ThreadPoolExecutor(10) as ex:
            results = list(ex.map(self.one, range(100)))
        for rc, out, err, tdir in results:
            self.assert_clean_exit(rc, err)
            self.assertEqual(rc, 0, err)
            self.assertEqual(out, b"unsat\n")
            outs = list(tdir.glob("*/*.out"))
            self.assertEqual(len(outs), 1)
            self.assertEqual(outs[0].read_bytes(), b"unsat\n")
            (tin,) = tdir.glob("*/*.in.smt2")
            self.assertTrue(tin.read_bytes().startswith(b"(check-sat)\n"))


class AyBinRequiredTest(ShimCase):
    """(d) AY_BIN has no default."""

    def test_unset(self):
        p = subprocess.run([sys.executable, str(SHIM), "-smt2", "-in"], stdin=subprocess.DEVNULL,
                           capture_output=True, env=self.env(AY_BIN=None), timeout=30)
        err = p.stderr.decode()
        self.assertEqual(p.returncode, 2)
        self.assertIn("AY_BIN is not set", err)
        self.assertEqual(p.stdout, b"")
        self.assertFalse(self.events.exists())

    def test_not_executable(self):
        p = subprocess.run([sys.executable, str(SHIM), "-smt2", "-in"], stdin=subprocess.DEVNULL,
                           capture_output=True, env=self.env(AY_BIN=str(self.tmp / "missing")), timeout=30)
        self.assertEqual(p.returncode, 2)
        self.assertIn("is not an executable file", p.stderr.decode())

    def test_z3_passthrough_needs_no_ay_bin(self):
        p = self.start(AY_BIN=None, SHIM_SOLVER=f"z3:{self.fake}")
        p.stdin.write(SESSION)
        p.stdin.close()
        rc, out, err = self.finish(p)
        self.assertEqual(rc, 0, err)
        self.assertTrue(out.startswith(b"unsat\n<<DONE>>\n"))


class OptionsTest(ShimCase):
    """End-state defaults, the two opt-outs, and the recorded event-log keys."""

    def run_session(self, **extra):
        p = self.start(FAKE_STDERR="c !! MODEL-UNCONFIRMED fake", FAKE_RLIMIT="100,5", **extra)
        p.stdin.write(SESSION)
        p.stdin.close()
        rc, out, err = self.finish(p)
        self.assertEqual(rc, 0, err)
        (ev,) = self.events_logged()
        return out, err, ev

    def test_default_args_are_z3_mode(self):
        out, err, ev = self.run_session(AY_SHIM_ARGS=None)
        self.assertEqual(ev["argv"], ["-q", "--z3-mode", "-smt2", "-in"])

    def test_defaults_forward_stderr_and_raw_rlimit(self):
        out, err, ev = self.run_session()
        self.assertIn("c !! MODEL-UNCONFIRMED fake", err)
        self.assertIn("c !! MODEL-UNCONFIRMED fake", ev["stderr_tail"])
        self.assertIn(b"(:rlimit-count 100 ", out)
        self.assertIn(b"(:rlimit-count 5 ", out)
        self.assertEqual(list(ev), RECORDED_KEYS + ["stderr_forwarded", "rlimit_monotone"])
        self.assertIs(ev["stderr_forwarded"], True)
        self.assertIs(ev["rlimit_monotone"], False)

    def test_opt_outs_restore_the_recorded_behaviour(self):
        out, err, ev = self.run_session(AY_SHIM_DROP_STDERR="1", AY_SHIM_RLIMIT_MONOTONE="1")
        self.assertNotIn("MODEL-UNCONFIRMED", err)
        self.assertIn("c !! MODEL-UNCONFIRMED fake", ev["stderr_tail"])
        self.assertIn(b"(:rlimit-count 100 ", out)
        self.assertIn(b"(:rlimit-count 105 ", out)   # monotone: 100, then 100 + 5
        self.assertEqual(list(ev), RECORDED_KEYS)

    def test_cpu_mode_keys(self):
        out, err, ev = self.run_session(AY_SHIM_DROP_STDERR="1", AY_SHIM_RLIMIT_MONOTONE="1",
                                        AY_SHIM_QUERY_CPU_S="60")
        self.assertEqual(list(ev), RECORDED_CPU_KEYS)
        self.assertIsNone(ev["kill_cpu_s"])

    def test_z3_passthrough_never_rewrites_rlimit(self):
        out, err, ev = self.run_session(AY_BIN=None, SHIM_SOLVER=f"z3:{self.fake}", AY_SHIM_DROP_STDERR="1",
                                        AY_SHIM_RLIMIT_MONOTONE="1")
        self.assertIn(b"(:rlimit-count 5 ", out)
        self.assertEqual(list(ev), RECORDED_KEYS)
        self.assertEqual(ev["solver"], str(self.fake))
        self.assertEqual(ev["argv"], ["-smt2", "-in"])

    def test_z3_passthrough_forwards_stderr_by_default(self):
        out, err, ev = self.run_session(AY_BIN=None, SHIM_SOLVER=f"z3:{self.fake}")
        self.assertIn("c !! MODEL-UNCONFIRMED fake", err)
        self.assertEqual(list(ev), RECORDED_KEYS + ["stderr_forwarded"])

    def test_transcripts_are_the_exact_bytes(self):
        tdir = self.tmp / "tx"
        out, err, ev = self.run_session(AY_SHIM_TRANSCRIPT_DIR=str(tdir))
        (tin,) = tdir.glob("*/*.in.smt2")
        (tout,) = tdir.glob("*/*.out")
        self.assertEqual(tin.read_bytes(), SESSION)
        self.assertEqual(tout.read_bytes(), out)


@unittest.skipUnless(os.environ.get("VERUS_BASELINE_ROOT"),
                     "set VERUS_BASELINE_ROOT to a recorded run tree to compare with the recorded shims")
class RecordedShimCompatibilityTest(ShimCase):
    """With both opt-outs set, this shim behaves as the recorded shims did: the same
    stdout, the same transcripts, the same event (up to pids and clocks)."""

    VOLATILE = {"pid", "start", "wall_s"}

    def compare(self, recorded_name, **extra):
        recorded = Path(os.environ["VERUS_BASELINE_ROOT"]).expanduser() / "bin" / recorded_name
        if not recorded.is_file():
            self.skipTest(f"{recorded} is not there")
        runs = {}
        for name, shim, opts in (("recorded", recorded, {}),
                                 ("landed", SHIM, {"AY_SHIM_DROP_STDERR": "1", "AY_SHIM_RLIMIT_MONOTONE": "1"})):
            ev_dir, tx_dir = self.tmp / f"{name}-ev", self.tmp / f"{name}-tx"
            p = self.start(shim=shim, FAKE_STDERR="c !! MODEL-UNCONFIRMED fake", FAKE_RLIMIT="100,5",
                           AY_SHIM_EVENT_DIR=str(ev_dir), AY_SHIM_TRANSCRIPT_DIR=str(tx_dir), **opts, **extra)
            p.stdin.write(SESSION)
            p.stdin.close()
            rc, out, err = self.finish(p)
            (ev,) = self.events_logged(ev_dir)
            tx = {f.suffix: f.read_bytes() for f in tx_dir.glob("*/*")}
            runs[name] = (rc, out, err, ev, tx)
        (rc_a, out_a, err_a, ev_a, tx_a), (rc_b, out_b, err_b, ev_b, tx_b) = runs["recorded"], runs["landed"]
        self.assertEqual((rc_a, out_a, err_a), (rc_b, out_b, err_b))
        self.assertEqual(tx_a, tx_b)
        self.assertEqual(list(ev_a), list(ev_b))
        strip = lambda ev: {k: ([a[:1] + a[2:] for a in v] if k == "answers" else v)
                            for k, v in ev.items() if k not in self.VOLATILE}
        self.assertEqual(strip(ev_a), strip(ev_b))

    def test_ay_mode(self):
        self.compare("ay-z3shim")

    def test_z3_passthrough(self):
        self.compare("ay-z3shim", AY_BIN=None, SHIM_SOLVER=f"z3:{self.fake}")

    def test_cpu_variant(self):
        self.compare("ay-z3shim-cpu", AY_SHIM_QUERY_CPU_S="60", AY_SHIM_QUERY_WALL_MAX_S="900")


if __name__ == "__main__":
    unittest.main()
