# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Own actual session roots until their group cleanup and direct reap complete.

This is process lifetime bookkeeping, never a compilation or proof capability.
It handles cooperative cancellation and Python exceptions; SIGKILL and machine
failure cannot run Python cleanup.
"""

import contextlib
import json
import os
import select
import signal
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

import session_owner
import native_request_channel


class Cancelled(RuntimeError):
    pass


class Registry:
    def __init__(self, native_channel=None):
        self.cancelled = None
        self.lock = threading.Lock()
        self.children = set()
        self.records = []
        self.record_path = None
        self.native_channel = native_channel

    def cancel(self, reason):
        # Also called by the main-thread signal handler: do not acquire a lock.
        if self.cancelled is None:
            self.cancelled = reason

    def check(self):
        if self.cancelled is not None:
            raise Cancelled(self.cancelled)

    def add(self, child):
        with self.lock:
            self.children.add(child)
            try:
                self.records.append(child.record)
            except BaseException:
                self.children.remove(child)
                raise

    def remove(self, child):
        with self.lock:
            self.children.remove(child)

    def cleanup(self):
        with self.lock:
            children = list(self.children)
        failures = []
        for child in children:
            try:
                child.finish()
            except BaseException as error:
                failures.append(error)
        if failures:
            raise failures[0]

    def write(self):
        if self.record_path is not None:
            with self.lock:
                records = list(self.records)
            self.record_path.write_text(json.dumps(
                {"cancelled": self.cancelled, "children": records}, indent=2) + "\n")


CURRENT = Registry()


class Child:
    def __init__(self, arguments, **kwargs):
        if not all(hasattr(os, name) for name in
                   ("waitid", "WNOWAIT", "WEXITED", "WNOHANG", "P_PID")):
            raise RuntimeError("owned suite execution needs native non-reaping waitid")
        CURRENT.check()
        self.registry = CURRENT
        self.lock = threading.Lock()
        self.closed = False
        self.cleanup_error = None
        self.protocol_error = None
        self.observation_error = None
        self.status_buffer = bytearray()
        self.status_eof = False
        self.registered = False
        passed = tuple(kwargs.pop("pass_fds", ()))
        # Validate existing caller descriptors before allocating private ones;
        # an unopened numeric locator cannot select a newly allocated report fd.
        for fd in passed:
            os.fstat(fd)
        environment = kwargs.pop("env", None)
        environment, passed = native_request_channel.bind(
            self.registry.native_channel,
            os.environ if environment is None else environment, passed)
        kwargs["env"] = environment
        status_read, status_write = os.pipe()
        try:
            life_read, self.life_write = os.pipe()
        except BaseException:
            os.close(status_read)
            os.close(status_write)
            raise
        self.status_read = status_read
        owner = Path(__file__).with_name("session_owner.py")
        owner_arguments = [sys.executable, "-I", "-S", str(owner),
                           str(status_write), str(life_read),
                           ",".join(str(fd) for fd in passed) if passed else "-",
                           "--", *map(str, arguments)]
        try:
            if set(passed) & {status_read, status_write, life_read, self.life_write}:
                raise RuntimeError("a caller descriptor changed into a private owner descriptor")
            os.set_blocking(status_read, False)
            self.process = subprocess.Popen(
                owner_arguments, start_new_session=True,
                pass_fds=(status_write, life_read, *passed), **kwargs)
        except BaseException:
            for fd in [status_read, status_write, life_read, self.life_write]:
                os.close(fd)
            raise
        os.close(status_write)
        os.close(life_read)
        self.record = {
            "owner_pid": self.process.pid, "owner_argv": owner_arguments,
            "command_argv": list(map(str, arguments)), "command_pid": None,
            "owner_from_actual_Popen": True, "owner_native_exit": None,
            "command_raw_exit": None, "command_direct_waited": False,
            "owner_raw_exit": None, "owner_direct_waited": False,
            "group_signal_delivered_before_owner_reap": False,
            "group_cleanup_error": None, "report_error": None,
            "owner_observation_error": None}
        try:
            self.registry.add(self)
            self.registered = True
        except BaseException:
            self.finish()
            raise

    def __enter__(self):
        try:
            self.registry.check()
        except BaseException:
            self.finish()
            raise
        return self

    def __exit__(self, *_error):
        self.finish()

    def _read_status(self, allow_missing=False):
        while not self.status_eof:
            try:
                data = os.read(self.status_read, 4096)
            except BlockingIOError:
                break
            if not data:
                self.status_eof = True
                break
            self.status_buffer.extend(data)
        while len(self.status_buffer) >= session_owner.FRAME.size:
            frame = bytes(self.status_buffer[:session_owner.FRAME.size])
            del self.status_buffer[:session_owner.FRAME.size]
            kind, pid, status = session_owner.FRAME.unpack(frame)
            if kind == b"B" and pid > 0 and status == 0 and self.record["command_pid"] is None:
                self.record["command_pid"] = pid
            elif (kind == b"X" and pid == self.record["command_pid"]
                  and not self.record["command_direct_waited"]):
                self.record["command_raw_exit"] = status
                self.record["command_direct_waited"] = True
            elif kind == b"F" and pid == 0 and self.record["command_pid"] is None:
                raise RuntimeError(f"session owner's actual command spawn failed: errno {status}")
            else:
                raise RuntimeError("invalid or repeated private command-status frame")
        if self.status_eof and self.status_buffer:
            raise RuntimeError("truncated private command-status frame")
        if self.status_eof and not allow_missing and not self.record["command_direct_waited"]:
            raise RuntimeError("session owner closed its report without actual command status")

    def _owner_exit(self):
        observed = os.waitid(os.P_PID, self.process.pid,
                             os.WEXITED | os.WNOHANG | os.WNOWAIT)
        if observed is not None:
            self.record["owner_native_exit"] = {
                "pid": observed.si_pid, "code": observed.si_code, "status": observed.si_status}
        return observed

    def exited(self):
        with self.lock:
            if self.closed:
                return True
            try:
                self._read_status()
            except BaseException as error:
                self.protocol_error = error
                self.record["report_error"] = repr(error)
                raise
            try:
                if self._owner_exit() is not None:
                    raise RuntimeError("the held session owner exited before group cleanup")
            except BaseException as error:
                self.observation_error = error
                self.record["owner_observation_error"] = repr(error)
                raise
            # Completion is its private actual command.wait() report, not
            # stdout EOF, owner status, a caller label, or a saved success.
            return self.record["command_direct_waited"]

    def finish(self):
        with self.lock:
            if self.closed:
                if self.cleanup_error is not None:
                    raise self.cleanup_error
                if self.protocol_error is not None:
                    raise self.protocol_error
                if self.observation_error is not None:
                    raise self.observation_error
                return self.record["command_raw_exit"]
            try:
                self._read_status(allow_missing=True)
            except BaseException as error:
                self.protocol_error = error
                self.record["report_error"] = repr(error)
            try:
                if self._owner_exit() is not None:
                    raise RuntimeError("the held session owner exited before group cleanup")
            except BaseException as error:
                self.observation_error = error
                self.record["owner_observation_error"] = repr(error)
            # The original actual Popen owner remains unreaped. A normally
            # completed command leaves this owner live and signalable.
            try:
                os.killpg(self.process.pid, signal.SIGKILL)
            except OSError as error:
                self.cleanup_error = error
                self.record["group_cleanup_error"] = {
                    "errno": error.errno, "type": type(error).__name__,
                    "message": str(error)}
            else:
                self.record["group_signal_delivered_before_owner_reap"] = True
            finally:
                os.close(self.life_write)
                # A refused group signal never excuses leaving our direct
                # owner unreaped and never establishes group emptiness.
                self.record["owner_raw_exit"] = self.process.wait()
                self.record["owner_direct_waited"] = True
                try:
                    self._read_status(allow_missing=True)
                except BaseException as error:
                    self.protocol_error = self.protocol_error or error
                    self.record["report_error"] = repr(self.protocol_error)
                finally:
                    os.close(self.status_read)
                    self.closed = True
                    if self.registered:
                        self.registry.remove(self)
            if self.cleanup_error is not None:
                raise self.cleanup_error
            if self.protocol_error is not None:
                raise self.protocol_error
            if self.observation_error is not None:
                raise self.observation_error
            # Hard cancellation may have killed the owner before its direct
            # command wait/report. UNKNOWN must not become the owner's -9.
            return self.record["command_raw_exit"]


def run(arguments, *, capture_output=False, text=False, timeout=None, check=False, **kwargs):
    """The runner's synchronous commands, with the same owned-root rule."""
    if capture_output:
        assert "stdout" not in kwargs and "stderr" not in kwargs
        kwargs.update(stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    kwargs.setdefault("stdin", subprocess.DEVNULL)
    readers, errors, output = [], [], {"stdout": None, "stderr": None}
    with Child(arguments, text=text, **kwargs) as child:
        def read(name, pipe):
            try:
                output[name] = pipe.read()
            except BaseException as error:
                errors.append(error)
        try:
            for name in ["stdout", "stderr"]:
                pipe = getattr(child.process, name)
                if pipe is not None:
                    thread = threading.Thread(target=read, args=(name, pipe))
                    thread.start()
                    readers.append(thread)
            deadline = None if timeout is None else time.monotonic() + timeout
            while not child.exited():
                child.registry.check()
                if errors:
                    raise errors[0]
                if deadline is not None and time.monotonic() >= deadline:
                    raise subprocess.TimeoutExpired(arguments, timeout)
                time.sleep(0.05)
        finally:
            try:
                child.finish()
            finally:
                for thread in readers:
                    thread.join()
                for name in ["stdout", "stderr"]:
                    pipe = getattr(child.process, name)
                    if pipe is not None:
                        pipe.close()
        if errors:
            raise errors[0]
        if child.record["command_raw_exit"] is None:
            raise RuntimeError("actual command status is unknown after owner termination")
        result = subprocess.CompletedProcess(arguments, child.record["command_raw_exit"],
                                             output["stdout"], output["stderr"])
        if check:
            result.check_returncode()
        return result


def parallel_map(function, values, workers):
    values = list(values)
    executor = ThreadPoolExecutor(max_workers=workers)
    futures = []
    try:
        futures = [executor.submit(function, value) for value in values]
        order = {future: index for index, future in enumerate(futures)}
        results = [None] * len(futures)
        for future in as_completed(futures):
            CURRENT.check()
            results[order[future]] = future.result()
        return results
    except BaseException:
        CURRENT.cancel("parallel worker failed or execution was cancelled")
        for future in futures:
            future.cancel()
        # Kill held actual roots before waiting for executor threads, whose
        # finally blocks then join readers and close their own files/pipes.
        CURRENT.cleanup()
        raise
    finally:
        executor.shutdown(wait=True, cancel_futures=True)


@contextlib.contextmanager
def scope(owned_stdin=False, native_channel=None):
    global CURRENT
    previous, CURRENT = CURRENT, Registry(native_channel)
    registry = CURRENT
    previous_handlers = {}
    stopped = False
    watcher = None
    def terminate(number, _frame):
        registry.cancel(f"signal {number}")
    def watch_input():
        try:
            while not stopped:
                readable, _, _ = select.select([sys.stdin], [], [], 0.1)
                if readable:
                    payload = os.read(sys.stdin.fileno(), 1)
                    registry.cancel("owner input closed" if not payload else "unexpected owner input")
                    return
        except BaseException as error:
            registry.cancel(f"owner input failed: {error}")
    try:
        for number in [signal.SIGINT, signal.SIGTERM]:
            previous_handlers[number] = signal.signal(number, terminate)
        if owned_stdin:
            watcher = threading.Thread(target=watch_input)
            watcher.start()
        yield registry
        registry.check()
    finally:
        if sys.exc_info()[0] is not None:
            registry.cancel("scope failed")
        try:
            registry.cleanup()
        finally:
            stopped = True
            if watcher is not None and watcher.ident is not None:
                watcher.join()
            for number, handler in previous_handlers.items():
                signal.signal(number, handler)
            try:
                registry.write()
            finally:
                CURRENT = previous
