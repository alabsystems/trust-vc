# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Own one actual native request socket. This transports data, never authority.

Capture at the executable's entry, before allocating pipes or opening files. An
environment value locates a borrowed descriptor; only the checked, owned socket
below can forward it. Rust descendants additionally need the supported std
NativeRequestChannel implementation; older std has no automatic handoff.
"""

import fcntl
import os
import socket
import stat

ENV = "TRUST_VC_NATIVE_REQUEST_FD"
_CONSTRUCT = object()


def _locator(value):
    if not isinstance(value, str) or not value.isascii() or not value.isdecimal():
        raise RuntimeError("native request locator must be a descriptor number")
    number = int(value)
    if number < 3 or str(number) != value:
        raise RuntimeError("native request locator must name a nonstandard descriptor")
    return number


def _identity(descriptor):
    metadata = os.fstat(descriptor)
    if not stat.S_ISSOCK(metadata.st_mode):
        raise RuntimeError("native request descriptor is not a socket")
    return metadata.st_dev, metadata.st_ino, metadata.st_mode


def _validate(endpoint):
    if (endpoint.family != socket.AF_UNIX
            or endpoint.getsockopt(socket.SOL_SOCKET, socket.SO_TYPE) != socket.SOCK_DGRAM):
        raise RuntimeError("native request channel must be an AF_UNIX datagram socket")
    # getpeername also rejects an unconnected datagram. Python normalizes
    # Darwin's zero-padded anonymous sockaddr into an empty address.
    if endpoint.getsockname() not in ("", b"") or endpoint.getpeername() not in ("", b""):
        raise RuntimeError("native request channel must be connected and anonymous")


class NativeRequestChannel:
    def __init__(self, token, endpoint, original):
        if token is not _CONSTRUCT:
            raise TypeError("capture a real inherited native request channel")
        self._endpoint = endpoint
        self._identity = _identity(endpoint.fileno())
        self._original = original

    def check(self):
        if _identity(self._endpoint.fileno()) != self._identity:
            raise RuntimeError("native request channel descriptor changed")
        _validate(self._endpoint)
        if os.get_inheritable(self._endpoint.fileno()):
            raise RuntimeError("retained native request channel must remain CLOEXEC")

    def bind(self, environment, resource_fds=()):
        """Compose existing caller descriptors with exactly this owned endpoint.

        The environment is rewritten to the actual duplicate, rather than
        treating the inherited numeric locator as an allowlist.
        """
        self.check()
        environment = dict(environment)
        if ENV in environment and _locator(environment[ENV]) not in (
                self._original, self._endpoint.fileno()):
            raise RuntimeError("native request channel locator was substituted")
        descriptors = tuple(resource_fds)
        for descriptor in descriptors:
            os.fstat(descriptor)
        descriptor = self._endpoint.fileno()
        environment[ENV] = str(descriptor)
        return environment, tuple(dict.fromkeys((*descriptors, descriptor)))

    def close(self):
        self._endpoint.close()

    def __enter__(self):
        self.check()
        return self

    def __exit__(self, *_error):
        self.close()


def capture(environment=None):
    """Validate before allocating, duplicate CLOEXEC, and leave the input open.

    No descriptor is allocated when the locator is absent, closed or names a
    regular file. Failure never closes a caller's borrowed descriptor.
    """
    environment = os.environ if environment is None else environment
    if ENV not in environment:
        return None
    original = _locator(environment[ENV])
    before = _identity(original)
    # A closed standard stream must never turn our locator into stdin/stdout.
    # Allocate the duplicate atomically CLOEXEC, above all three standard FDs.
    duplicate = fcntl.fcntl(original, fcntl.F_DUPFD_CLOEXEC, 3)
    endpoint = None
    try:
        os.set_inheritable(duplicate, False)
        endpoint = socket.socket(fileno=duplicate)
        _validate(endpoint)
        if _identity(original) != before or _identity(duplicate) != before:
            raise RuntimeError("native request descriptor changed during capture")
        # The borrowed inherited locator is no longer implicitly inheritable.
        # The owned duplicate is the only endpoint forwarded by this utility.
        os.set_inheritable(original, False)
        return NativeRequestChannel(_CONSTRUCT, endpoint, original)
    except BaseException:
        if endpoint is None:
            os.close(duplicate)
        else:
            endpoint.close()
        raise


def bind(channel, environment, resource_fds=()):
    if channel is None:
        if ENV in environment:
            raise RuntimeError("native request locator has no captured socket")
        return environment, tuple(resource_fds)
    return channel.bind(environment, resource_fds)
