# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Keep a real session owner live after its unchanged command has exited.

The private report is process bookkeeping, not verifier output or permission.
The command does not inherit either private descriptor. On hard cancellation
the owner can die before reporting its command; callers must retain UNKNOWN.
"""

import os
import sys

# -I intentionally omits the script directory. Select only this maintained
# sibling module and capture before allocating any owner report/private pipes.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import native_request_channel
_CHANNEL = native_request_channel.capture() if __name__ == "__main__" else None

import struct
import subprocess

FRAME = struct.Struct("!cqi")


def report(descriptor, kind, pid, status):
    message = FRAME.pack(kind, pid, status)
    if os.write(descriptor, message) != len(message):
        raise RuntimeError("short private process-status write")


def main():
    descriptor, liveness = int(sys.argv[1]), int(sys.argv[2])
    passed = () if sys.argv[3] == "-" else tuple(int(value) for value in sys.argv[3].split(","))
    if sys.argv[4] != "--" or not sys.argv[5:]:
        raise RuntimeError("invalid session-owner invocation")
    if descriptor in passed or liveness in passed:
        raise RuntimeError("a private owner descriptor cannot be a command descriptor")
    if _CHANNEL is not None:
        received = int(os.environ[native_request_channel.ENV])
        if passed.count(received) != 1 or received in (descriptor, liveness):
            raise RuntimeError("native request channel is not the selected command descriptor")
        passed = tuple(fd for fd in passed if fd != received)
    environment, passed = native_request_channel.bind(_CHANNEL, os.environ, passed)
    # pass_fds made these inheritable for this exact owner's exec. Restore
    # CLOEXEC before creating the genuine command, and never pass them to it.
    os.set_inheritable(descriptor, False)
    os.set_inheritable(liveness, False)
    try:
        command = subprocess.Popen(sys.argv[5:], close_fds=True, pass_fds=passed,
                                   env=environment)
    except OSError as error:
        report(descriptor, b"F", 0, error.errno)
        raise
    report(descriptor, b"B", command.pid, 0)
    # The real command inherited precisely these standard descriptors. The
    # bookkeeping owner must not keep its stdout/stderr pipes open afterward.
    for descriptor_number in [0, 1, 2]:
        os.close(descriptor_number)
    status = command.wait()
    report(descriptor, b"X", command.pid, status)
    os.close(descriptor)
    # Retain this original, signalable session owner until its parent cleans
    # the held group. EOF also permits direct reap on a refused signal.
    while os.read(liveness, 1):
        pass
    os.close(liveness)


if __name__ == "__main__":
    try:
        main()
    finally:
        if _CHANNEL is not None:
            _CHANNEL.close()
