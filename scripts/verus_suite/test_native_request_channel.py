# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Real Darwin descriptor/exec controls; these do not run a verifier or own an SDK."""

import json
import os
import socket
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import native_request_channel as channel
import owned_processes as owned


class NativeChannelTest(unittest.TestCase):
    def setUp(self):
        self.previous = owned.CURRENT
        self.directory = tempfile.TemporaryDirectory(prefix="native-channel-")
        self.root = Path(self.directory.name).resolve()
        self.server, self.client = socket.socketpair(socket.AF_UNIX, socket.SOCK_DGRAM)
        self.server.settimeout(3)

    def tearDown(self):
        owned.CURRENT.cleanup()
        owned.CURRENT = self.previous
        self.client.close()
        self.server.close()
        self.directory.cleanup()

    def capture(self):
        return channel.capture({channel.ENV: str(self.client.fileno())})

    def test_real_channel_survives_borrowed_close_and_stays_cloexec(self):
        with self.capture() as endpoint:
            self.client.close()
            environment, descriptors = endpoint.bind({})
            descriptor, = descriptors
            self.assertFalse(os.get_inheritable(descriptor))
            borrowed = socket.socket(fileno=descriptor)
            try:
                borrowed.send(b"actual owned duplicate")
            finally:
                borrowed.detach()
            self.assertEqual(self.server.recv(128), b"actual owned duplicate")
            self.assertEqual(environment[channel.ENV], str(descriptor))
        with self.assertRaises(OSError):
            os.fstat(descriptor)

    def test_wrong_socket_kinds_names_unconnected_and_nonsockets_refuse(self):
        with tempfile.TemporaryFile() as regular:
            wrong = [regular.fileno()]
            with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as internet, \
                    socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM) as unconnected:
                wrong += [internet.fileno(), unconnected.fileno()]
                for descriptor in wrong:
                    with self.subTest(descriptor=descriptor), self.assertRaises((OSError, RuntimeError)):
                        channel.capture({channel.ENV: str(descriptor)})
                    os.fstat(descriptor)  # failure leaves the borrowed handle open
            first, second = socket.socketpair(socket.AF_UNIX, socket.SOCK_STREAM)
            try:
                with self.assertRaisesRegex(RuntimeError, "datagram"):
                    channel.capture({channel.ENV: str(first.fileno())})
            finally:
                first.close()
                second.close()
        with socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM) as named:
            named.bind(str(self.root / "named"))
            named.connect(str(self.root / "named"))
            with self.assertRaisesRegex(RuntimeError, "anonymous"):
                channel.capture({channel.ENV: str(named.fileno())})

    def test_only_exact_nonstandard_live_locator_is_accepted(self):
        for locator in ("0", "1", "2", "03", "-3", "3,4", " 3", "٣", "", "999999"):
            with self.subTest(locator=locator), self.assertRaises((OSError, RuntimeError)):
                channel.capture({channel.ENV: locator})
        self.assertIsNone(channel.capture({}))
        with self.capture() as endpoint:
            with self.assertRaisesRegex(RuntimeError, "substituted"):
                endpoint.bind({channel.ENV: "999999"})
        with self.assertRaises((OSError, ValueError)):
            endpoint.bind({})

    def test_actual_owned_owner_command_chain_composes_one_resource_fd(self):
        source = ("import os,socket,json,sys\n"
                  f"sys.path.insert(0,{str(Path(__file__).parent)!r})\n"
                  "import native_request_channel as n\n"
                  "with n.capture() as c:\n"
                  " env,fds=c.bind({})\n"
                  " s=socket.socket(fileno=fds[0])\n"
                  " s.send(b'command through real owner')\n"
                  " s.detach()\n"
                  " data=os.read(int(sys.argv[1]),99).decode()\n"
                  " print(json.dumps({'data':data,'cloexec':not os.get_inheritable(fds[0]),'fds':fds}))\n")
        read, write = os.pipe()
        try:
            os.write(write, b"existing resource descriptor")
            os.close(write)
            write = None
            with self.capture() as endpoint:
                owned.CURRENT = owned.Registry(endpoint)
                result = owned.run([sys.executable, "-c", source, str(read)], pass_fds=(read,),
                                   capture_output=True, text=True, timeout=10, env={"PATH": os.defpath})
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(self.server.recv(128), b"command through real owner")
                observed = json.loads(result.stdout)
                self.assertEqual(observed["data"], "existing resource descriptor")
                self.assertTrue(observed["cloexec"])
                self.assertEqual(len(observed["fds"]), 1)
                endpoint.check()
                record, = owned.CURRENT.records
                self.assertTrue(record["command_direct_waited"])
                self.assertTrue(record["owner_direct_waited"])
                self.assertTrue(record["group_signal_delivered_before_owner_reap"])
                self.assertEqual(record["command_raw_exit"], 0)
        finally:
            os.close(read)
            if write is not None:
                os.close(write)

    def test_uncaptured_environment_locator_cannot_launch_a_child(self):
        owned.CURRENT = owned.Registry()
        with self.assertRaisesRegex(RuntimeError, "no captured socket"):
            owned.run([sys.executable, "-c", "raise SystemExit(99)"],
                      env={channel.ENV: str(self.client.fileno())})
        self.assertFalse(owned.CURRENT.records)

    def test_supported_isolated_entry_captures_before_help_or_private_pipes(self):
        runner = Path(__file__).with_name("run_suite.py")
        environment = {"PATH": os.defpath, channel.ENV: str(self.client.fileno())}
        result = subprocess.run([sys.executable, "-I", "-S", str(runner), "--help"],
            env=environment, pass_fds=(self.client.fileno(),), capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("--prepared-sdk-request", result.stdout)
        # The parent's borrowed endpoint was neither consumed nor closed.
        self.client.send(b"parent still owns borrowed channel")
        self.assertEqual(self.server.recv(128), b"parent still owns borrowed channel")
        environment[channel.ENV] = "999999"
        refused = subprocess.run([sys.executable, "-I", "-S", str(runner), "--help"],
            env=environment, capture_output=True, text=True, timeout=10)
        self.assertNotEqual(refused.returncode, 0)
        self.assertNotIn("usage:", refused.stdout)
        self.assertIn("Bad file descriptor", refused.stderr)

    def test_closed_standard_streams_cannot_become_the_owned_locator(self):
        program = ("import os,sys,socket\n"
                   f"sys.path.insert(0,{str(Path(__file__).parent)!r})\n"
                   "import native_request_channel as n\n"
                   "for fd in (0,1,2): os.close(fd)\n"
                   "with n.capture() as endpoint:\n"
                   " env,fds=endpoint.bind({})\n"
                   " s=socket.socket(fileno=fds[0])\n"
                   " s.send(str(fds[0]).encode())\n"
                   " s.detach()\n"
                   "os._exit(0)\n")
        result = subprocess.run([sys.executable, "-c", program],
            env={channel.ENV: str(self.client.fileno())}, pass_fds=(self.client.fileno(),),
            capture_output=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertGreaterEqual(int(self.server.recv(128)), 3)

    def test_reused_socket_and_unopened_resource_locator_cannot_select_private_fds(self):
        with self.capture() as endpoint:
            owned.CURRENT = owned.Registry(endpoint)
            closed = os.dup(self.client.fileno())
            os.close(closed)
            with self.assertRaises(OSError):
                owned.Child([sys.executable, "-c", "raise SystemExit(99)"], pass_fds=(closed,))
            self.assertFalse(owned.CURRENT.records)
            _environment, descriptors = endpoint.bind({})
            replacement, peer = socket.socketpair(socket.AF_UNIX, socket.SOCK_DGRAM)
            try:
                os.dup2(replacement.fileno(), descriptors[0], inheritable=False)
                with self.assertRaisesRegex(RuntimeError, "descriptor changed"):
                    endpoint.bind({})
            finally:
                replacement.close()
                peer.close()



if __name__ == "__main__":
    unittest.main()
