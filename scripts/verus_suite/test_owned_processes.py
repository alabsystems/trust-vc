# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Real process lifetime controls, not verifier programs or proof doubles."""

import json
import os
import socket
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parent))
import owned_processes as owned
import run_suite


class OwnedProcessTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="sl-", dir="/tmp/.ubd")
        self.root = Path(self.directory.name)
        self.previous = owned.CURRENT
        owned.CURRENT = owned.Registry()

    def tearDown(self):
        try:
            owned.CURRENT.cancel("control finished")
            owned.CURRENT.cleanup()
            self.assertFalse(owned.CURRENT.children)
            for record in owned.CURRENT.records:
                self.assertTrue(record["group_signal_delivered_before_owner_reap"])
                self.assertTrue(record["owner_direct_waited"])
        finally:
            owned.CURRENT = self.previous
            self.directory.cleanup()

    def program(self, source):
        path = self.root / "child.py"
        path.write_text(source)
        return [sys.executable, str(path)]

    def test_live_owner_preserves_actual_command_exit_before_owner_reap(self):
        program = '''
import json,os,sys
opened=[]
for name in os.listdir('/dev/fd'):
    try:
        fd=int(name)
        os.fstat(fd)
        opened.append(fd)
    except (ValueError,OSError):
        pass
print(json.dumps({'pid':os.getpid(),'argv':sys.argv[1:],'cwd':os.getcwd(),
                  'value':os.environ['OWNED_CONTROL_DATA'],'fds':opened}),flush=True)
raise SystemExit(23)
'''
        env = dict(os.environ, OWNED_CONTROL_DATA="ordinary data")
        with owned.Child([sys.executable, "-c", program, "two words"],
                         cwd=self.root, env=env, stdout=subprocess.PIPE, text=True) as child:
            with child.process.stdout:
                deadline = time.monotonic() + 5
                while not child.exited():
                    self.assertLess(time.monotonic(), deadline)
                    time.sleep(0.01)
                # The command was directly waited; its original Popen owner
                # is still live and unreaped, with no stdout writer retained.
                self.assertIsNone(os.waitid(os.P_PID, child.process.pid,
                                            os.WEXITED | os.WNOHANG | os.WNOWAIT))
                observed = json.loads(child.process.stdout.read())
                self.assertEqual(observed["pid"], child.record["command_pid"])
                self.assertNotEqual(observed["pid"], child.process.pid)
                self.assertEqual(observed["argv"], ["two words"])
                self.assertEqual(observed["cwd"], str(self.root.resolve()))
                self.assertEqual(observed["value"], "ordinary data")
                self.assertFalse(set(observed["fds"]) - {0, 1, 2})
                self.assertEqual(child.record["command_raw_exit"], 23)
                self.assertTrue(child.record["command_direct_waited"])
                self.assertEqual(child.finish(), 23)
                self.assertEqual(child.finish(), 23)
                self.assertEqual(child.record["owner_raw_exit"], -9)
                self.assertTrue(child.record["owner_direct_waited"])

    def test_stdout_eof_does_not_kill_a_live_root_or_hide_exit19(self):
        started = time.monotonic()
        result = owned.run([sys.executable, "-c",
                            "import os,time; os.close(1); time.sleep(.2); raise SystemExit(19)"],
                           capture_output=True, text=True)
        self.assertGreaterEqual(time.monotonic() - started, 0.2)
        self.assertEqual(result.returncode, 19)
        self.assertEqual(result.stdout, "")

    def test_suite_ok_followed_by_exit19_is_a_failure(self):
        events = [{"type": "suite", "event": "started", "test_count": 1},
                  {"type": "test", "event": "started", "name": "case"},
                  {"type": "test", "event": "ok", "name": "case"},
                  {"type": "suite", "event": "ok", "passed": 1, "failed": 0}]
        binary = self.program("import os,time\n"
                              + "print(" + repr("\n".join(json.dumps(e) for e in events))
                              + ", flush=True)\nos.close(1)\ntime.sleep(.2)\nraise SystemExit(19)\n")
        args = SimpleNamespace(bin_wall=5, test_stall=2, max_attempts=1, threads=1,
                               include_ignored=False)
        result = run_suite.run_binary("control", binary, dict(os.environ), self.root,
                                      args, self.root, {"case": {"ignore": False}})
        self.assertEqual(result["attempts"][0]["rc"], 19)
        self.assertIn("exit 19", result["attempts"][0]["reason"])
        self.assertEqual(result["results"]["case"]["outcome"], "crashed")

    def test_suite_success_without_command_exit_hits_wall_and_stays_failed(self):
        events = [{"type": "suite", "event": "started", "test_count": 1},
                  {"type": "test", "event": "started", "name": "case"},
                  {"type": "test", "event": "ok", "name": "case"},
                  {"type": "suite", "event": "ok", "passed": 1, "failed": 0}]
        binary = self.program("import os,time\n"
                              + "print(" + repr("\n".join(json.dumps(e) for e in events))
                              + ", flush=True)\nos.close(1)\ntime.sleep(6)\n")
        args = SimpleNamespace(bin_wall=.25, test_stall=2, max_attempts=1, threads=1,
                               include_ignored=False)
        started = time.monotonic()
        result = run_suite.run_binary("control", binary, dict(os.environ), self.root,
                                      args, self.root, {"case": {"ignore": False}})
        self.assertEqual(set(result["results"]), {"case"})
        self.assertEqual(len(result["attempts"]), 1)
        self.assertEqual(result["attempts"][0]["reason"], "wall")
        self.assertIsNone(result["attempts"][0]["rc"])
        self.assertEqual(result["results"]["case"]["outcome"], "timeout")
        self.assertIn("did not finish cleanly", result["results"]["case"]["message"])
        self.assertEqual(owned.CURRENT.records[-1]["owner_raw_exit"], -9)
        self.assertIsNone(owned.CURRENT.records[-1]["command_raw_exit"])
        self.assertLess(time.monotonic() - started, 4)

    def test_malformed_json_stream_cannot_bypass_the_existing_wall_limit(self):
        binary = self.program("import time\n"
                              "end=time.monotonic()+6\n"
                              "while time.monotonic()<end:\n"
                              " print('malformed JSON',flush=True)\n"
                              " time.sleep(.001)\n")
        started = time.monotonic()
        result, running, reason, status = run_suite.run_attempt(
            binary, None, dict(os.environ), self.root, 1, 2,
            started + .25, self.root / "malformed", 1)
        self.assertEqual(reason, "wall")
        self.assertIsNone(status)
        self.assertIsNone(owned.CURRENT.records[-1]["command_raw_exit"])
        self.assertFalse(owned.CURRENT.records[-1]["command_direct_waited"])
        self.assertEqual(owned.CURRENT.records[-1]["owner_raw_exit"], -9)
        self.assertFalse(result)
        self.assertFalse(running)
        self.assertLess(time.monotonic() - started, 4)

    def connected_program(self, server_path, invalid_output=False, exit_status=None):
        # Both actual processes retain the socket writer. EOF on the accepted
        # peer proves group cleanup closed both, without adopting any PID.
        inner = "import time;time.sleep(120)"
        return self.program(
            "import socket,subprocess,sys,time,os\n"
            + "s=socket.socket(socket.AF_UNIX);s.connect(" + repr(str(server_path)) + ")\n"
            + "p=subprocess.Popen([sys.executable,'-c'," + repr(inner)
            + "],pass_fds=(s.fileno(),),stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)\ns.sendall(b'ready')\n"
            + ("os.write(1,b'\\xff');os.close(1)\n" if invalid_output else "")
            + ("time.sleep(120)\n" if exit_status is None
               else "raise SystemExit(" + str(exit_status) + ")\n"))

    def test_discovery_worker_failure_cleans_roots_before_executor_shutdown(self):
        server = socket.socket(socket.AF_UNIX)
        server.bind(str(self.root / "socket")); server.listen(); server.settimeout(5)
        binary = self.connected_program(self.root / "socket")
        failures = []
        ready = threading.Event()
        def task(which):
            if which == "fail":
                self.assertTrue(ready.wait(5))
                raise RuntimeError("real companion discovery failed")
            return run_suite.list_tests(binary, dict(os.environ), self.root)
        def execute():
            try:
                owned.parallel_map(task, ["discover", "fail"], 2)
            except BaseException as error:
                failures.append(error)
        thread = threading.Thread(target=execute)
        thread.start()
        try:
            peer, _ = server.accept()
            with peer:
                peer.settimeout(5)
                self.assertEqual(peer.recv(5), b"ready")
                ready.set()
                thread.join(5)
                self.assertFalse(thread.is_alive())
                self.assertEqual(peer.recv(1), b"")
            self.assertEqual(len(failures), 1)
            self.assertIn("companion discovery failed", str(failures[0]))
        finally:
            ready.set()
            owned.CURRENT.cancel("control cleanup")
            owned.CURRENT.cleanup()
            thread.join()
            server.close()

    def test_actual_command23_and_socket_descendant_cleanup_are_distinct_from_owner_wait(self):
        with socket.socket(socket.AF_UNIX) as server:
            server.bind(str(self.root / "socket")); server.listen(); server.settimeout(5)
            binary = self.connected_program(self.root / "socket", exit_status=23)
            results, failures = [], []
            def execute():
                try:
                    results.append(owned.run(binary, capture_output=True, text=True))
                except BaseException as error:
                    failures.append(error)
            thread = threading.Thread(target=execute)
            thread.start()
            try:
                peer, _ = server.accept()
                with peer:
                    peer.settimeout(5)
                    self.assertEqual(peer.recv(5), b"ready")
                    thread.join(5)
                    self.assertFalse(thread.is_alive())
                    self.assertEqual(peer.recv(1), b"")
                self.assertFalse(failures)
                self.assertEqual(len(results), 1)
                self.assertEqual(results[0].returncode, 23)
                record = owned.CURRENT.records[-1]
                self.assertEqual(record["command_raw_exit"], 23)
                self.assertTrue(record["command_direct_waited"])
                self.assertEqual(record["owner_raw_exit"], -9)
                self.assertTrue(record["owner_direct_waited"])
            finally:
                owned.CURRENT.cancel("control cleanup")
                owned.CURRENT.cleanup()
                thread.join()

    def test_output_decoder_failure_closes_pipes_and_the_real_process_tree(self):
        with socket.socket(socket.AF_UNIX) as server:
            server.bind(str(self.root / "socket")); server.listen(); server.settimeout(5)
            binary = self.connected_program(self.root / "socket", invalid_output=True)
            failures = []
            def execute():
                try:
                    owned.run(binary, capture_output=True, text=True)
                except BaseException as error:
                    failures.append(error)
            thread = threading.Thread(target=execute)
            thread.start()
            try:
                peer, _ = server.accept()
                with peer:
                    peer.settimeout(5)
                    self.assertEqual(peer.recv(5), b"ready")
                    thread.join(5)
                    self.assertFalse(thread.is_alive())
                    self.assertEqual(peer.recv(1), b"")
                self.assertEqual(len(failures), 1)
                self.assertIsInstance(failures[0], UnicodeDecodeError)
            finally:
                owned.CURRENT.cancel("control cleanup")
                owned.CURRENT.cleanup()
                thread.join()

    def scope_cancellation(self, via_pipe):
        record = self.root / "nested-record.json"
        program = """
import os,pathlib,signal,subprocess,sys,time
sys.path.insert(0,sys.argv[1])
import owned_processes as owned
with owned.scope(owned_stdin=sys.argv[3]=='pipe') as registry:
    registry.record_path=pathlib.Path(sys.argv[2])
    with owned.Child([sys.executable,'-u','-c',
                      "import time;print('ready',flush=True);time.sleep(120)"],
                     stdout=subprocess.PIPE,text=True) as child:
        with child.process.stdout:
            child.process.stdout.readline()
            print('ready',flush=True)
            with registry.lock:
                if sys.argv[3]=='signal':
                    sys.stdin.buffer.read(1)
                    os.kill(os.getpid(),signal.SIGTERM)
                while True:
                    registry.check()
                    time.sleep(.02)
"""
        with owned.Child([sys.executable, "-u", "-c", program,
                          str(Path(owned.__file__).parent), str(record),
                          "pipe" if via_pipe else "signal"],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True) as child:
            try:
                self.assertEqual(child.process.stdout.readline().strip(), "ready")
                if via_pipe:
                    child.process.stdin.close()
                else:
                    child.process.stdin.write("T")
                    child.process.stdin.flush()
                deadline = time.monotonic() + 5
                while not child.exited():
                    self.assertLess(time.monotonic(), deadline)
                    time.sleep(.01)
                self.assertEqual(child.finish(), 1)
                observed = json.loads(record.read_text())
                self.assertEqual(observed["cancelled"],
                                 "owner input closed" if via_pipe else "signal 15")
                self.assertEqual(len(observed["children"]), 1)
                self.assertTrue(observed["children"][0]["group_signal_delivered_before_owner_reap"])
                self.assertTrue(observed["children"][0]["owner_direct_waited"])
                self.assertIsNone(observed["children"][0]["command_raw_exit"])
                self.assertFalse(observed["children"][0]["command_direct_waited"])
                self.assertEqual(observed["children"][0]["owner_raw_exit"], -9)
            finally:
                child.finish()
                for name in ["stdin", "stdout", "stderr"]:
                    getattr(child.process, name).close()

    def test_owned_pipe_eof_cleans_a_separate_session(self):
        self.scope_cancellation(via_pipe=True)

    def test_sigterm_does_not_reacquire_the_interrupted_registry_lock(self):
        self.scope_cancellation(via_pipe=False)


if __name__ == "__main__":
    unittest.main()
