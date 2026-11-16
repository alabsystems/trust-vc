// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::mem::{self, size_of};
use std::os::fd::{FromRawFd, OwnedFd, RawFd};

const REQUEST: [u8; 8] = *b"TVCREQ2\0";
const STOP: [u8; 8] = *b"TVCEND2\0";

pub(super) fn no_sigpipe(fd: BorrowedFd<'_>) -> io::Result<()> {
    #[cfg(target_os = "macos")]
    {
        let yes: libc::c_int = 1;
        // SAFETY: this borrows a live descriptor and a correctly sized value.
        let rc = unsafe {
            libc::setsockopt(
                fd.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_NOSIGPIPE,
                (&yes as *const libc::c_int).cast(),
                size_of::<libc::c_int>() as _,
            )
        };
        if rc != 0 {
            return Err(io::Error::last_os_error());
        }
    }
    let _ = fd;
    Ok(())
}

pub(super) fn validate_socket(fd: BorrowedFd<'_>, kind: libc::c_int) -> io::Result<()> {
    let mut actual: libc::c_int = 0;
    let mut size = size_of::<libc::c_int>() as libc::socklen_t;
    // SAFETY: all output buffers are fully initialized and correctly sized.
    let rc = unsafe {
        libc::getsockopt(
            fd.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_TYPE,
            (&mut actual as *mut libc::c_int).cast(),
            &mut size,
        )
    };
    if rc != 0 {
        return Err(io::Error::last_os_error());
    }
    if actual != kind || size as usize != size_of::<libc::c_int>() {
        return Err(invalid("wrong native channel socket type"));
    }
    for peer in [false, true] {
        // SAFETY: sockaddr_un is a C output buffer, initialized before use.
        let mut address: libc::sockaddr_un = unsafe { mem::zeroed() };
        let mut length = size_of::<libc::sockaddr_un>() as libc::socklen_t;
        let rc = unsafe {
            if peer {
                libc::getpeername(
                    fd.as_raw_fd(),
                    (&mut address as *mut libc::sockaddr_un).cast(),
                    &mut length,
                )
            } else {
                libc::getsockname(
                    fd.as_raw_fd(),
                    (&mut address as *mut libc::sockaddr_un).cast(),
                    &mut length,
                )
            }
        };
        if rc != 0 {
            return Err(io::Error::last_os_error());
        }
        let header = mem::offset_of!(libc::sockaddr_un, sun_path);
        #[cfg(target_os = "macos")]
        let anonymous = (length as usize == header
            || length as usize == size_of::<libc::sockaddr>())
            && address.sun_len as usize == length as usize
            && address
                .sun_path
                .iter()
                .take((length as usize).saturating_sub(header))
                .all(|byte| *byte == 0);
        // Linux abstract names can contain only zero bytes. A padded address
        // is still named there, so only the actual no-address header is valid.
        #[cfg(not(target_os = "macos"))]
        let anonymous = length as usize == header;
        if address.sun_family as libc::c_int != libc::AF_UNIX || !anonymous {
            return Err(invalid("native channel must be connected and anonymous"));
        }
    }
    Ok(())
}

pub(super) fn send(socket: &UnixDatagram, reply: Option<BorrowedFd<'_>>) -> io::Result<()> {
    send_inner(socket, reply, None)
}

pub(super) fn send_until(
    socket: &UnixDatagram,
    reply: Option<BorrowedFd<'_>>,
    deadline: std::time::Instant,
) -> io::Result<()> {
    send_inner(socket, reply, Some(deadline))
}

fn send_inner(
    socket: &UnixDatagram,
    reply: Option<BorrowedFd<'_>>,
    deadline: Option<std::time::Instant>,
) -> io::Result<()> {
    let bytes = if reply.is_some() { REQUEST } else { STOP };
    let mut iov = libc::iovec {
        iov_base: bytes.as_ptr().cast_mut().cast(),
        iov_len: bytes.len(),
    };
    // usize alignment suffices for every cmsghdr on the supported native hosts.
    let mut ancillary = [0usize; 8];
    let mut message: libc::msghdr = unsafe { mem::zeroed() };
    message.msg_iov = &mut iov;
    message.msg_iovlen = 1;
    if let Some(reply) = reply {
        message.msg_control = ancillary.as_mut_ptr().cast();
        message.msg_controllen = unsafe { libc::CMSG_SPACE(size_of::<RawFd>() as _) } as _;
        // SAFETY: the initialized message owns sufficient aligned CMSG_SPACE.
        unsafe {
            let header = libc::CMSG_FIRSTHDR(&message);
            (*header).cmsg_level = libc::SOL_SOCKET;
            (*header).cmsg_type = libc::SCM_RIGHTS;
            (*header).cmsg_len = libc::CMSG_LEN(size_of::<RawFd>() as _) as _;
            std::ptr::write_unaligned(libc::CMSG_DATA(header).cast::<RawFd>(), reply.as_raw_fd());
        }
    }
    #[cfg(target_os = "linux")]
    let flags = libc::MSG_NOSIGNAL;
    #[cfg(not(target_os = "linux"))]
    let flags = 0;
    let flags = flags
        | if deadline.is_some() {
            libc::MSG_DONTWAIT
        } else {
            0
        };
    loop {
        if let Some(deadline) = deadline {
            remaining(deadline)?;
        }
        // SAFETY: message borrows its live buffers and optional live reply FD.
        let sent = unsafe { libc::sendmsg(socket.as_raw_fd(), &message, flags) };
        if sent == bytes.len() as isize {
            return Ok(());
        }
        if sent >= 0 {
            return Err(invalid("partial native control datagram"));
        }
        let error = io::Error::last_os_error();
        if error.kind() == io::ErrorKind::Interrupted {
            continue;
        }
        if error.kind() == io::ErrorKind::WouldBlock {
            if let Some(deadline) = deadline {
                let duration = remaining(deadline)?;
                let milliseconds =
                    duration.as_millis().saturating_add(1).min(i32::MAX as u128) as i32;
                let mut ready = libc::pollfd {
                    fd: socket.as_raw_fd(),
                    events: libc::POLLOUT,
                    revents: 0,
                };
                let polled = unsafe { libc::poll(&mut ready, 1, milliseconds) };
                if polled < 0 {
                    let error = io::Error::last_os_error();
                    if error.kind() != io::ErrorKind::Interrupted {
                        return Err(error);
                    }
                }
                if ready.revents & (libc::POLLERR | libc::POLLHUP | libc::POLLNVAL) != 0 {
                    return Err(io::Error::new(
                        io::ErrorKind::BrokenPipe,
                        "native control channel closed",
                    ));
                }
                continue;
            }
        }
        return Err(error);
    }
}

pub(super) fn receive(socket: &UnixDatagram) -> io::Result<Option<UnixStream>> {
    let mut bytes = [0u8; 8];
    let mut iov = libc::iovec {
        iov_base: bytes.as_mut_ptr().cast(),
        iov_len: bytes.len(),
    };
    // Darwin installs all rights before truncating ancillary copyout. Reserve
    // the full admissible native control payload, not merely one wanted FD:
    // XNU UIPC_MAX_CMSG_FD is512 and sockargs bounds MT_CONTROL by MCLBYTES.
    // Four KiB covers CMSG_SPACE(512*sizeof(RawFd)); Linux permits253 rights.
    // See Apple's bsd/kern/{uipc_usrreq,uipc_syscalls}.c and Linux unix(7).
    let mut ancillary = [0usize; 512];
    #[cfg(target_os = "linux")]
    let flags = libc::MSG_CMSG_CLOEXEC;
    #[cfg(not(target_os = "linux"))]
    let flags = 0;
    let (received, message) = loop {
        let mut message: libc::msghdr = unsafe { mem::zeroed() };
        message.msg_iov = &mut iov;
        message.msg_iovlen = 1;
        message.msg_control = ancillary.as_mut_ptr().cast();
        message.msg_controllen = mem::size_of_val(&ancillary) as _;
        let count = unsafe { libc::recvmsg(socket.as_raw_fd(), &mut message, flags) };
        if count >= 0 {
            break (count as usize, message);
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(error);
        }
    };
    let mut rights = Vec::<OwnedFd>::new();
    let mut malformed = false;
    // Kernel-delivered SCM_RIGHTS are owned even when the frame is rejected.
    // Collect every delivered FD before validation so every error closes them.
    unsafe {
        let mut header = libc::CMSG_FIRSTHDR(&message);
        while !header.is_null() {
            let base = libc::CMSG_LEN(0) as usize;
            let size = (*header).cmsg_len as usize;
            let offset = header as usize - ancillary.as_ptr() as usize;
            if size < base
                || offset
                    .checked_add(size)
                    .is_none_or(|n| n > message.msg_controllen as usize)
            {
                malformed = true;
                break;
            }
            if (*header).cmsg_level == libc::SOL_SOCKET && (*header).cmsg_type == libc::SCM_RIGHTS {
                let count = (size - base) / size_of::<RawFd>();
                malformed |= (size - base) % size_of::<RawFd>() != 0;
                for index in 0..count {
                    let fd = std::ptr::read_unaligned(
                        libc::CMSG_DATA(header).cast::<RawFd>().add(index),
                    );
                    rights.push(OwnedFd::from_raw_fd(fd));
                }
            } else {
                malformed = true;
            }
            header = libc::CMSG_NXTHDR(&message, header);
        }
    }
    for fd in &rights {
        // Darwin's caller guarantees no concurrent exec until this completes.
        let flags = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETFD) };
        if flags < 0
            || unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, flags | libc::FD_CLOEXEC) } < 0
        {
            return Err(io::Error::last_os_error());
        }
    }
    if malformed
        || message.msg_flags & (libc::MSG_TRUNC | libc::MSG_CTRUNC) != 0
        || received != bytes.len()
    {
        return Err(invalid("malformed native control datagram"));
    }
    if bytes == STOP && rights.is_empty() {
        return Ok(None);
    }
    if bytes != REQUEST || rights.len() != 1 {
        return Err(invalid("wrong native request handle count"));
    }
    let reply = rights.pop().unwrap();
    validate_socket(reply.as_fd(), libc::SOCK_STREAM)?;
    no_sigpipe(reply.as_fd())?;
    Ok(Some(UnixStream::from(reply)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw(socket: &UnixDatagram, bytes: &[u8], files: &[BorrowedFd<'_>]) {
        let mut iov = libc::iovec {
            iov_base: bytes.as_ptr().cast_mut().cast(),
            iov_len: bytes.len(),
        };
        let mut ancillary = [0usize; 128];
        let mut message: libc::msghdr = unsafe { mem::zeroed() };
        message.msg_iov = &mut iov;
        message.msg_iovlen = 1;
        if !files.is_empty() {
            let size = files.len() * size_of::<RawFd>();
            assert!(size <= 128 * size_of::<RawFd>());
            message.msg_control = ancillary.as_mut_ptr().cast();
            message.msg_controllen = unsafe { libc::CMSG_SPACE(size as _) } as _;
            unsafe {
                let header = libc::CMSG_FIRSTHDR(&message);
                (*header).cmsg_level = libc::SOL_SOCKET;
                (*header).cmsg_type = libc::SCM_RIGHTS;
                (*header).cmsg_len = libc::CMSG_LEN(size as _) as _;
                for (index, file) in files.iter().enumerate() {
                    std::ptr::write_unaligned(
                        libc::CMSG_DATA(header).cast::<RawFd>().add(index),
                        file.as_raw_fd(),
                    );
                }
            }
        }
        assert_eq!(
            unsafe { libc::sendmsg(socket.as_raw_fd(), &message, 0) },
            bytes.len() as isize
        );
    }

    #[test]
    fn malformed_ancillary_closes_every_delivered_descriptor() {
        let (server, client) = pair().unwrap();
        let file = std::fs::File::open("/dev/null").unwrap();
        let count = || std::fs::read_dir("/dev/fd").unwrap().count();
        let before = count();
        for _ in 0..8 {
            let mut oversized = REQUEST.to_vec();
            oversized.push(99);
            for (bytes, n) in [
                (REQUEST.as_slice(), 0),
                (STOP.as_slice(), 1),
                (b"UNKNOWN!".as_slice(), 1),
                (REQUEST.as_slice(), 2),
                (REQUEST.as_slice(), 32),
                (REQUEST.as_slice(), 128),
                (oversized.as_slice(), 1),
            ] {
                let files = (0..n).map(|_| file.as_fd()).collect::<Vec<_>>();
                raw(&client.control, bytes, &files);
                // SAFETY: no same-process exec occurs in this control test.
                assert!(unsafe { server.receive(Some(Duration::from_secs(2))) }.is_err());
                assert_eq!(count(), before, "rejected ancillary leaked a descriptor");
            }
        }
        assert!(file.metadata().is_ok());
    }
}
