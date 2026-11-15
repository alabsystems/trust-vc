#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Measurement shim: stand in for z3 under Verus AIR, which launches "$VERUS_Z3_PATH -smt2 -in".

A suite run does NOT need this shim. Point VERUS_Z3_PATH at a symlink NAMED z3
that points at ay (ay turns on its z3 mode when its executable is called z3)
and pass VERUS_EXTRA_ARGS="-V no-solver-version-check --smt-option timeout=<ms>";
README.md says why and what was measured. Use this shim when a run has to be
MEASURED query by query, or compared with z3 behind the same logging.

What it does:
  * runs the ay binary named by AY_BIN with AY_SHIM_ARGS (default "-q --z3-mode")
    plus the caller's flags (-smt2 -in). AY_BIN is REQUIRED: there is no default
    path, because a default once pointed at a stale build and silently measured
    the wrong solver. --z3-mode is ay's documented z3 drop-in mode, and the
    recorded runs passed it explicitly; without it ay prints its native
    reason-unknown words (timeout, incomplete, ...), which AIR does not accept;
  * forwards the solver's stderr to AIR, exactly as a solver launched directly
    would (AIR does not redirect it, and the Verus test harness fails a test on
    every non-JSON stderr line), and ALSO records it in the event log.
    AY_SHIM_DROP_STDERR=1 keeps it away from AIR instead, as the recorded
    2026-09-23 runs did; that turned z3's own 4,114 ok into 4,113
    (triggers::test_trigger_on_lambda_3 needs z3's stderr warning);
  * forwards ":rlimit-count N" unchanged. AY_SHIM_RLIMIT_MONOTONE=1 rewrites it
    to a monotone counter, as the recorded ay runs did: AIR
    (air/src/smt_verify.rs:547-548) subtracts successive readings, but only
    within one query, and ay's counter only goes down across a query boundary
    (measured: 216 decreases in 3,169 readings, all at a boundary). The value
    only feeds Verus's profiling statistics, never a verdict. The rewrite never
    applies to SHIM_SOLVER=z3;
and adds, for measurement only (nothing here changes an answer the solver gives):
  * a per-(check-sat) budget. By default it is wall time: when the solver has not
    answered a check-sat within AY_SHIM_QUERY_WALL_S seconds (60), it is killed.
    With AY_SHIM_QUERY_CPU_S set, it is CPU time instead: the solver is killed
    once its process tree (the supervisor and its children, read with ps) has
    used that many CPU seconds on the pending check-sat, or after
    AY_SHIM_QUERY_WALL_MAX_S seconds of wall time (900), a backstop. A wall
    budget is load-sensitive, a CPU budget is not. AIR then sees the pipe close.
    The kill is recorded in the event log, so a timeout is never mistaken for a
    crash; in CPU mode each event also records "kill_cpu_s" (CPU the tree used
    on the pending check-sat), "kill_pending_s" (its wall time) and
    "kill_loadavg";
  * an event log (AY_SHIM_EVENT_DIR): one JSON line per solver process with the
    test it served, every check-sat answer with its duration and the sha256 of
    the whole command stream up to that (check-sat) (the same query sent to z3
    and to ay has the same hash, so answers can be compared query by query), every
    reason-unknown and (error ...) line, the solver's exit status and the tail of
    its stderr. When stderr is forwarded the event carries "stderr_forwarded":
    true, and when ay's :rlimit-count is forwarded unchanged it carries
    "rlimit_monotone": false;
  * optional transcripts (AY_SHIM_TRANSCRIPT_DIR): the exact bytes AIR sent and
    the exact bytes the solver answered, per solver process.

SHIM_SOLVER=z3:<path> runs that z3 with the original arguments instead of ay,
so the same logging and transcripts can be captured for the reference solver.

Each answer in the event log is [answer, seconds, prefix-hash] plus, for an
unknown, the reason-unknown line that followed it.

Recorded runs. With AY_SHIM_DROP_STDERR=1 and AY_SHIM_RLIMIT_MONOTONE=1 the event
log (the same keys in the same order), the transcripts, the prefix hashes and the
SHIM_SOLVER=z3 passthrough are those of the shim behind the recorded 2026-09-23
runs, and with AY_SHIM_QUERY_CPU_S set as well, those of its CPU-budget variant.
The pairing tools (classify.py, and the root-cause tools kept with ay's diagnoses)
depend on the prefix hashes.

Exiting. The stdin thread is blocked in a read whenever the shim exits for a
reason other than AIR closing stdin: ay killed at the wall, ay exiting on its own,
a signal. A thread blocked in sys.stdin.buffer.readline holds that BufferedReader's
lock, and Python 3.9's interpreter shutdown takes it to close sys.stdin, so it
aborted ("Fatal Python error: _enter_buffered_busy", SIGABRT, printed to the
stderr AIR shares with the harness, and one macOS Python crash report per solver
process). The stdin thread therefore reads fd 0 with os.read, which takes no lock;
that alone makes every exit path safe. The normal path still ends with os._exit.
"""
import hashlib
import json
import os
import re
import select
import subprocess
import sys
import threading
import time

AY = ""
AY_ARGS = []
QUERY_WALL = 60.0
QUERY_CPU = None         # set: CPU-budget mode (AY_SHIM_QUERY_CPU_S)
EOF_GRACE = 10.0
EVENT_DIR = ""
TRANSCRIPT_DIR = ""
SOLVER = "ay"
DROP_STDERR = False
RLIMIT_MONOTONE = False

T0 = None
KEY = None
argv = None
p = None


def die(msg):
    sys.stderr.write(f"ay_z3shim.py: {msg}\n")
    sys.stderr.flush()
    sys.exit(2)


def env_seconds(name, default):
    raw = os.environ.get(name, default)
    try:
        return float(raw)
    except ValueError:
        die(f"{name}={raw!r} is not a number of seconds")


def load_config():
    """Read the environment. AY_BIN has no default (see the module docstring)."""
    global AY, AY_ARGS, QUERY_WALL, QUERY_CPU, EOF_GRACE, EVENT_DIR, TRANSCRIPT_DIR, SOLVER
    global DROP_STDERR, RLIMIT_MONOTONE
    AY = os.environ.get("AY_BIN", "")
    AY_ARGS = os.environ.get("AY_SHIM_ARGS", "-q --z3-mode").split()
    if os.environ.get("AY_SHIM_QUERY_CPU_S", ""):
        QUERY_CPU = env_seconds("AY_SHIM_QUERY_CPU_S", "60")
        QUERY_WALL = env_seconds("AY_SHIM_QUERY_WALL_MAX_S", "900")
    else:
        QUERY_CPU = None
        QUERY_WALL = env_seconds("AY_SHIM_QUERY_WALL_S", "60")
    EOF_GRACE = env_seconds("AY_SHIM_EOF_GRACE_S", "10")
    EVENT_DIR = os.environ.get("AY_SHIM_EVENT_DIR", "")
    TRANSCRIPT_DIR = os.environ.get("AY_SHIM_TRANSCRIPT_DIR", "")
    SOLVER = os.environ.get("SHIM_SOLVER", "ay")
    DROP_STDERR = os.environ.get("AY_SHIM_DROP_STDERR", "") == "1"
    RLIMIT_MONOTONE = os.environ.get("AY_SHIM_RLIMIT_MONOTONE", "") == "1"
    if not SOLVER.startswith("z3:"):
        if not AY:
            die("AY_BIN is not set. Set it to the ay binary to measure; there is no default, "
                "because a default path once measured a stale build without saying so. "
                "(SHIM_SOLVER=z3:<path> runs z3 instead.)")
        if not (os.path.isfile(AY) and os.access(AY, os.X_OK)):
            die(f"AY_BIN={AY!r} is not an executable file")


def test_key():
    """The Verus harness passes <target>/test_inputs/<binary>-<test>/<entry>.rs to
    rust_verify, which is this process's parent."""
    try:
        args = subprocess.run(["ps", "-o", "args=", "-p", str(os.getppid())],
                              capture_output=True, text=True, timeout=10).stdout
    except Exception:
        args = ""
    m = re.search(r"test_inputs/([^/ ]+)/", args)
    return m.group(1) if m else f"unknown-ppid{os.getppid()}"


transcript_errors = []
stderr_forward_errors = []


class Transcript:
    """One transcript file, written by one thread and closed by another. It is
    unbuffered, so it holds no buffer lock, needs no flush at exit and keeps
    every byte up to a SIGKILL. The lock serialises write and close, so a line
    that arrives after the close is dropped rather than raising. A failure
    (missing directory, full disk) ends that transcript, is recorded in the
    event log, and never interrupts the traffic between AIR and the solver."""

    def __init__(self, path):
        self.lock = threading.Lock()
        self.f = None
        try:
            self.f = open(path, "wb", buffering=0)
        except OSError as e:
            transcript_errors.append(f"open {path}: {e}")

    def write(self, data):
        with self.lock:
            if self.f is None:
                return
            try:
                view = memoryview(data)
                while view:
                    view = view[self.f.write(view):]
            except OSError as e:
                transcript_errors.append(f"write {self.f.name}: {e}")
                self.close_locked()

    def close(self):
        with self.lock:
            self.close_locked()

    def close_locked(self):
        f, self.f = self.f, None
        if f is not None:
            try:
                f.close()
            except OSError as e:
                transcript_errors.append(f"close {f.name}: {e}")


tin = tout = None
lock = threading.Lock()
state = {
    "pending_since": None,   # time the oldest unanswered (check-sat) was sent
    "pending": 0,
    "answers": [],           # [answer, seconds]
    "reason_unknown": [],
    "errors": [],
    "killed": None,
    "after_kill": [],        # stdout lines that arrived after the wall kill (not forwarded)
    "stdin_eof": None,
    "stdin_bytes": 0,
    "prefix": [],            # sha256 of every byte AIR sent up to and including each (check-sat)
}
stream_hash = hashlib.sha256()
stderr_tail = bytearray()


def stdin_lines():
    """The lines of fd 0, split exactly as BufferedReader.readline splits them
    (after each b"\\n"; a final unterminated line is yielded at EOF). Read with
    os.read rather than sys.stdin.buffer: see "Exiting" in the module docstring.
    A read that would block waits for input; any other read error is taken as
    end of input, so the session ends the way it does when AIR closes stdin."""
    buf = bytearray()
    while True:
        try:
            chunk = os.read(0, 1 << 16)
        except BlockingIOError:
            select.select([0], [], [])
            continue
        except OSError:
            break
        if not chunk:
            break
        scan = len(buf)  # buf holds no b"\n" here: every complete line was yielded
        buf += chunk
        start = 0
        nl = buf.find(b"\n", scan)
        while nl >= 0:
            yield bytes(buf[start:nl + 1])
            start = nl + 1
            nl = buf.find(b"\n", start)
        del buf[:start]
    if buf:
        yield bytes(buf)


def pump_stdin():
    try:
        for line in stdin_lines():
            state["stdin_bytes"] += len(line)
            stream_hash.update(line)
            if tin:
                tin.write(line)
            if line.strip() == b"(check-sat)":
                with lock:
                    state["prefix"].append(stream_hash.hexdigest()[:20])
                    if state["pending"] == 0:
                        state["pending_since"] = time.time()
                    state["pending"] += 1
            try:
                p.stdin.write(line)
                if line.endswith(b"\n") and line.startswith(b"(echo"):
                    p.stdin.flush()
            except (BrokenPipeError, OSError):
                break
    finally:
        state["stdin_eof"] = time.time()
        try:
            p.stdin.close()
        except OSError:
            pass


def forward_stderr(chunk):
    """Write to fd 2 with os.write, which takes no lock (see "Exiting"). A failed
    write stops the forwarding, is recorded in the event log, and never stops the
    recording."""
    view = memoryview(chunk)
    try:
        while view:
            view = view[os.write(2, view):]
    except OSError as e:
        stderr_forward_errors.append(str(e))


def pump_stderr():
    for chunk in iter(lambda: p.stderr.read(4096), b""):
        stderr_tail.extend(chunk)
        if len(stderr_tail) > 16384:
            del stderr_tail[:len(stderr_tail) - 8192]
        if not DROP_STDERR and not stderr_forward_errors:
            forward_stderr(chunk)


def watchdog():
    """Wall-time budget per check-sat (the default)."""
    while p.poll() is None:
        time.sleep(0.5)
        now = time.time()
        with lock:
            since = state["pending_since"]
        if since is not None and now - since > QUERY_WALL:
            state["killed"] = f"check-sat unanswered after {QUERY_WALL:g} s"
            p.kill()
            return
        eof = state["stdin_eof"]
        if eof is not None and now - eof > EOF_GRACE and since is None:
            state["killed"] = f"no exit {EOF_GRACE:g} s after stdin EOF"
            p.kill()
            return


def tree_cpu():
    """CPU seconds (user+sys) used so far by ay's supervisor and its children."""
    try:
        kids = subprocess.run(["pgrep", "-P", str(p.pid)], capture_output=True, text=True,
                              timeout=5).stdout.split()
        out = subprocess.run(["ps", "-o", "time=", "-p", ",".join([str(p.pid)] + kids)],
                             capture_output=True, text=True, timeout=5).stdout.split()
    except Exception:
        return None
    tot = 0.0
    for t in out:
        sec = 0.0
        for x in t.split(":"):
            sec = sec * 60 + float(x)
        tot += sec
    return tot


def watchdog_cpu():
    """CPU-time budget per check-sat (AY_SHIM_QUERY_CPU_S), with a wall backstop."""
    seen_since = None
    cpu0 = 0.0
    last_poll = 0.0
    while p.poll() is None:
        time.sleep(0.5)
        now = time.time()
        with lock:
            since = state["pending_since"]
        if since is None:
            seen_since = None
            eof = state["stdin_eof"]
            if eof is not None and now - eof > EOF_GRACE:
                state["killed"] = f"no exit {EOF_GRACE:g} s after stdin EOF"
                p.kill()
                return
            continue
        if since != seen_since:
            seen_since = since
            c = tree_cpu()
            cpu0 = c if c is not None else 0.0
            last_poll = now
            continue
        cpu_used = None
        if now - last_poll >= 2.0:
            last_poll = now
            c = tree_cpu()
            cpu_used = (c - cpu0) if c is not None else None
        over_cpu = cpu_used is not None and cpu_used >= QUERY_CPU
        if over_cpu or now - since > QUERY_WALL:
            state["killed"] = (f"check-sat unanswered after {QUERY_CPU:g} CPU s" if over_cpu
                               else f"check-sat unanswered after {QUERY_WALL:g} wall s")
            state["kill_cpu_s"] = round(cpu_used, 2) if cpu_used is not None else None
            state["kill_pending_s"] = round(now - since, 2)
            state["kill_loadavg"] = round(os.getloadavg()[0], 2)
            p.kill()
            return


def main():
    global T0, KEY, argv, p, tin, tout
    load_config()
    T0 = time.time()
    KEY = test_key()

    if SOLVER.startswith("z3:"):
        argv = [SOLVER[3:]] + sys.argv[1:]
        rewrite_rlimit = False
    else:
        argv = [AY] + AY_ARGS + sys.argv[1:]
        rewrite_rlimit = RLIMIT_MONOTONE

    p = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, bufsize=0)

    if TRANSCRIPT_DIR:
        d = os.path.join(TRANSCRIPT_DIR, KEY)
        stem = os.path.join(d, f"{int(T0 * 1000)}-{os.getpid()}")
        try:
            os.makedirs(d, exist_ok=True)
        except OSError as e:
            transcript_errors.append(f"makedirs {d}: {e}")
        tin = Transcript(stem + ".in.smt2")
        tout = Transcript(stem + ".out")

    threading.Thread(target=pump_stdin, daemon=True).start()
    stderr_thread = threading.Thread(target=pump_stderr, daemon=True)
    stderr_thread.start()
    threading.Thread(target=watchdog_cpu if QUERY_CPU is not None else watchdog, daemon=True).start()

    rx = re.compile(rb"(:rlimit-count\s+)(\d+)")
    counter = 0
    out = sys.stdout.buffer
    ANS = {b"sat", b"unsat", b"unknown"}
    try:
        for line in iter(p.stdout.readline, b""):
            if state["killed"]:
                # ay's worker can still flush a line (e.g. "unknown") after the shim
                # killed the supervisor; that is not an answer ay gave in time.
                state["after_kill"].append(line.decode(errors="replace").strip()[:200])
                continue
            s = line.strip()
            if s in ANS:
                with lock:
                    since = state["pending_since"]
                    i = len(state["answers"])
                    h = state["prefix"][i] if i < len(state["prefix"]) else None
                    state["answers"].append([s.decode(), round(time.time() - since, 3) if since else None, h])
                    state["pending"] = max(0, state["pending"] - 1)
                    state["pending_since"] = time.time() if state["pending"] else None
            elif s.startswith(b"(:reason-unknown"):
                r = s.decode(errors="replace")[:300]
                state["reason_unknown"].append(r)
                with lock:
                    if state["answers"] and len(state["answers"][-1]) == 3:
                        state["answers"][-1].append(r)
            elif s.startswith(b"(error"):
                if len(state["errors"]) < 20:
                    state["errors"].append(s.decode(errors="replace")[:500])
            if rewrite_rlimit:
                m = rx.search(line)
                if m:
                    counter += max(1, int(m.group(2)))
                    line = rx.sub(lambda mm: mm.group(1) + str(counter).encode(), line)
            if tout:
                tout.write(line)
            out.write(line)
            out.flush()
    except BrokenPipeError:
        pass
    rc = p.wait()
    stderr_thread.join(timeout=5)  # read the solver's last stderr bytes before logging them
    if tout:
        tout.close()
    if tin:
        tin.close()

    if EVENT_DIR:
        ev = {
            "test": KEY,
            "pid": os.getpid(),
            "solver": argv[0],
            "argv": argv[1:],
            "start": round(T0, 3),
            "wall_s": round(time.time() - T0, 3),
            "rc": rc,
            "killed": state["killed"],
        }
        if QUERY_CPU is not None:
            ev["kill_cpu_s"] = state.get("kill_cpu_s")
            ev["kill_pending_s"] = state.get("kill_pending_s")
            ev["kill_loadavg"] = state.get("kill_loadavg")
        ev.update({
            "after_kill": state["after_kill"][:5],
            "pending_at_exit": state["pending"],
            "answers": state["answers"],
            "unanswered_prefix": state["prefix"][len(state["answers"]):],
            "reason_unknown": state["reason_unknown"],
            "errors": state["errors"],
            "stdin_bytes": state["stdin_bytes"],
            "stderr_tail": bytes(stderr_tail[-3000:]).decode(errors="replace"),
        })
        # keys the recorded runs never had appear only when an option departs from them
        if not DROP_STDERR:
            ev["stderr_forwarded"] = True
            if stderr_forward_errors:
                ev["stderr_forward_errors"] = stderr_forward_errors[:5]
        if not SOLVER.startswith("z3:") and not RLIMIT_MONOTONE:
            ev["rlimit_monotone"] = False
        if transcript_errors:
            ev["transcript_errors"] = transcript_errors[:5]
        try:
            os.makedirs(EVENT_DIR, exist_ok=True)
            fd = os.open(os.path.join(EVENT_DIR, KEY + ".jsonl"), os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
            os.write(fd, (json.dumps(ev) + "\n").encode())
            os.close(fd)
        except OSError:
            pass
    try:
        out.flush()
    except (BrokenPipeError, OSError):
        pass
    os._exit(0 if rc == 0 else (rc if rc > 0 else 1))


if __name__ == "__main__":
    main()
