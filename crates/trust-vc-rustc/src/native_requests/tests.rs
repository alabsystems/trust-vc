// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::Arc;
use std::thread;
const TRANSPORT_WAIT: Duration = Duration::from_secs(10);

fn request(label: &str) -> Request {
    Request {
        argv: vec![
            "original-rust_verify".into(),
            "--extern".into(),
            label.into(),
            OsString::from_vec(vec![b'x', 0xff, b'y']),
        ],
        cwd: PathBuf::from(OsString::from_vec(vec![b'/', b't', 0xfe])),
        outputs: OutputContext::from_pairs([
            ("TRUST_VC_VERDICT_DIR".into(), "/original/verdicts".into()),
            ("TRUST_VC_DUMP_VCIR".into(), "original-dump".into()),
        ])
        .unwrap(),
        verusdoc: Some(OsString::from_vec(b"raw-doc-\xff".to_vec())),
    }
}

fn incoming(server: &Coordinator) -> Incoming {
    // SAFETY: the test receives between callbacks, without concurrent exec.
    unsafe { server.receive(Some(TRANSPORT_WAIT)) }
        .unwrap()
        .unwrap()
}

#[test]
fn byte_exact_request_outputs_and_explicit_shutdown() {
    let (server, client) = pair().unwrap();
    let expected = request("real-request");
    let sender_expected = expected.clone();
    let sender = thread::spawn(move || {
        let response = client.submit(&sender_expected, TRANSPORT_WAIT).unwrap();
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let status = response.copy_to(&mut out, &mut err).unwrap();
        assert_eq!(status, 37);
        assert_eq!(out, b"stdout\0\xff");
        assert_eq!(err, b"diagnostic\n\xfe");
        client.stop().unwrap();
    });
    let received = incoming(&server);
    assert_ne!(
        unsafe { libc::fcntl(received.socket.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC,
        0
    );
    let (actual, mut reply) = received.read(TRANSPORT_WAIT).unwrap();
    assert_eq!(actual, expected);
    reply.stdout(b"stdout\0\xff").unwrap();
    reply.stderr(b"diagnostic\n\xfe").unwrap();
    reply.finish(37).unwrap();
    assert!(unsafe { server.receive(Some(TRANSPORT_WAIT)) }
        .unwrap()
        .is_none());
    sender.join().unwrap();
}

#[test]
fn concurrent_descendants_cannot_mix_replies() {
    let (server, client) = pair().unwrap();
    let client = Arc::new(client);
    let senders = (0..12)
        .map(|n| {
            let client = Arc::clone(&client);
            thread::spawn(move || {
                let label = format!("client-{n}");
                let response = client.submit(&request(&label), TRANSPORT_WAIT).unwrap();
                let (mut out, mut err) = (Vec::new(), Vec::new());
                assert_eq!(response.copy_to(&mut out, &mut err).unwrap(), n);
                assert_eq!(out, label.as_bytes());
                assert_eq!(err, vec![n; MAX_OUTPUT_FRAME + 17]);
            })
        })
        .collect::<Vec<_>>();
    for _ in 0..senders.len() {
        let (actual, mut reply) = incoming(&server).read(TRANSPORT_WAIT).unwrap();
        let label = actual.argv[2].to_str().unwrap();
        let n: u8 = label.strip_prefix("client-").unwrap().parse().unwrap();
        reply.stdout(label.as_bytes()).unwrap();
        reply.stderr(&vec![n; MAX_OUTPUT_FRAME + 17]).unwrap();
        reply.finish(n).unwrap();
    }
    for sender in senders {
        sender.join().unwrap();
    }
}

#[test]
fn closed_and_partial_callbacks_never_complete_successfully() {
    let (server, client) = pair().unwrap();
    let sender = thread::spawn(move || {
        let response = client
            .submit(&request("closed-callback"), TRANSPORT_WAIT)
            .unwrap();
        assert!(response.copy_to(&mut Vec::new(), &mut Vec::new()).is_err());
    });
    let (_, mut reply) = incoming(&server).read(TRANSPORT_WAIT).unwrap();
    reply.stdout(b"partial output").unwrap();
    drop(reply);
    sender.join().unwrap();
    let (server, client) = pair().unwrap();
    drop(server);
    assert!(client
        .submit(&request("closed-server"), TRANSPORT_WAIT)
        .is_err());
}

#[test]
fn closed_sender_and_oversize_frame_refuse_before_callback() {
    let (server, client) = pair().unwrap();
    let (mut local, remote) = UnixStream::pair().unwrap();
    control::send(&client.control, Some(remote.as_fd())).unwrap();
    drop(remote);
    local
        .write_all(&((MAX_REQUEST_BYTES + 1) as u32).to_be_bytes())
        .unwrap();
    local.shutdown(std::net::Shutdown::Write).unwrap();
    assert!(incoming(&server).read(TRANSPORT_WAIT).is_err());
    let (local, remote) = UnixStream::pair().unwrap();
    control::send(&client.control, Some(remote.as_fd())).unwrap();
    drop(remote);
    drop(local);
    // Darwin may reject the now-unconnected peer during control validation;
    // other hosts deliver the endpoint and report EOF while decoding.
    match unsafe { server.receive(Some(TRANSPORT_WAIT)) } {
        Ok(Some(received)) => assert!(received.read(TRANSPORT_WAIT).is_err()),
        Err(_) => {}
        Ok(None) => panic!("closed request was mistaken for a stop frame"),
    }
    let mut oversized = request("oversize");
    oversized
        .argv
        .push(OsString::from_vec(vec![b'a'; MAX_REQUEST_BYTES]));
    assert!(client.submit(&oversized, TRANSPORT_WAIT).is_err());
    assert!(unsafe { server.receive(Some(Duration::from_millis(10))) }.is_err());
}

#[test]
fn wrong_handles_and_unrepresented_environment_are_refused() {
    let (server, client) = pair().unwrap();
    let file = std::fs::File::open("/dev/null").unwrap();
    assert!(Client::from_inherited(file.as_fd()).is_err());
    assert!(file.metadata().is_ok()); // failed validation did not take custody
    control::send(&client.control, Some(file.as_fd())).unwrap();
    assert!(unsafe { server.receive(Some(TRANSPORT_WAIT)) }.is_err());
    let (wrong, _) = UnixDatagram::pair().unwrap();
    control::send(&client.control, Some(wrong.as_fd())).unwrap();
    assert!(unsafe { server.receive(Some(TRANSPORT_WAIT)) }.is_err());
    // Real named local and peer addresses remain refused on every host.
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = PathBuf::from("/tmp").join(format!("tvc-{}-{unique}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let a = directory.join("a");
    let b = directory.join("b");
    let named_a = UnixDatagram::bind(&a).unwrap();
    let named_b = UnixDatagram::bind(&b).unwrap();
    named_a.connect(&b).unwrap();
    named_b.connect(&a).unwrap();
    assert!(Client::from_inherited(named_a.as_fd()).is_err());
    let stream_path = directory.join("stream");
    let listener = std::os::unix::net::UnixListener::bind(&stream_path).unwrap();
    let connected = UnixStream::connect(&stream_path).unwrap();
    let (accepted, _) = listener.accept().unwrap();
    assert!(control::validate_socket(accepted.as_fd(), libc::SOCK_STREAM).is_err());
    assert!(control::validate_socket(connected.as_fd(), libc::SOCK_STREAM).is_err());
    drop((named_a, named_b, listener, connected, accepted));
    for path in [a, b, stream_path] {
        std::fs::remove_file(path).unwrap();
    }
    std::fs::remove_dir(directory).unwrap();
    for key in [
        "VSTD_KIND",
        "RUSTC",
        "BUILD_SLOT_HELD",
        "CARGO_MAKEFLAGS",
        "OWNER",
    ] {
        assert!(OutputContext::from_pairs([(key.into(), "1".into())]).is_err());
    }
    assert!(OutputContext::from_pairs([
        ("TRUST_VC_VERDICT_DIR".into(), "one".into()),
        ("TRUST_VC_VERDICT_DIR".into(), "two".into()),
    ])
    .is_err());
}

#[test]
fn malformed_wire_and_trailing_or_incomplete_response_fail_closed() {
    let good = wire::encode_request(&request("wire")).unwrap();
    for length in 0..good.len() {
        assert!(wire::decode_request(&good[..length]).is_err());
    }
    let mut extra = good;
    extra.push(0);
    assert!(wire::decode_request(&extra).is_err());
    for bytes in [
        vec![],
        vec![3],
        vec![3, 0, 7],
        vec![1, 0, 1, 0, 1],
        vec![99],
    ] {
        let (mut writer, reader) = UnixStream::pair().unwrap();
        writer.write_all(&bytes).unwrap();
        drop(writer);
        assert!(Response { socket: reader }
            .copy_to(&mut Vec::new(), &mut Vec::new())
            .is_err());
    }
}

#[test]
fn documentation_context_preserves_absence_empty_bytes_and_rejects_old_wire() {
    for value in [
        None,
        Some(OsString::new()),
        Some("1".into()),
        Some(OsString::from_vec(b"doc-\xff".to_vec())),
    ] {
        let mut original = request("doc-context");
        original.verusdoc = value;
        let bytes = wire::encode_request(&original).unwrap();
        assert_eq!(wire::decode_request(&bytes).unwrap(), original);
        let mut old = bytes;
        old[..8].copy_from_slice(b"TVCARGV2");
        assert!(wire::decode_request(&old).is_err());
    }
}

#[test]
fn inherited_child_request() {
    let Some(raw) = std::env::var_os(INHERITED_CONTROL_ENV) else {
        return;
    };
    let raw: i32 = raw.to_str().unwrap().parse().unwrap();
    // SAFETY: only this test's real parent supplies an inherited FD locator;
    // validation borrows it, and no arbitrary descriptor is adopted or closed.
    let borrowed = unsafe { BorrowedFd::borrow_raw(raw) };
    let client = Client::from_inherited(borrowed).unwrap();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    assert_eq!(
        client
            .submit(&request("actual-inherited-child"), TRANSPORT_WAIT)
            .unwrap()
            .copy_to(&mut out, &mut err)
            .unwrap(),
        0
    );
    assert_eq!(out, b"native inherited reply");
    assert!(err.is_empty());
}

#[test]
fn actual_inherited_channel_child_is_directly_joined() {
    let (server, client) = pair().unwrap();
    let mut command = std::process::Command::new(std::env::current_exe().unwrap());
    command.args([
        "--exact",
        "native_requests::tests::inherited_child_request",
        "--nocapture",
    ]);
    let child = client.spawn(command).unwrap();
    let (actual, mut reply) = incoming(&server).read(TRANSPORT_WAIT).unwrap();
    assert_eq!(actual.argv[2], "actual-inherited-child");
    reply.stdout(b"native inherited reply").unwrap();
    reply.finish(0).unwrap();
    assert!(child.wait().unwrap().success());
}

#[test]
fn coordinator_callback_error_and_admission_deadline_fail_closed() {
    let (server, client) = pair().unwrap();
    let sender = thread::spawn(move || {
        let response = client
            .submit(&request("callback-error"), TRANSPORT_WAIT)
            .unwrap();
        assert!(response.copy_to(&mut Vec::new(), &mut Vec::new()).is_err());
    });
    let mut called = false;
    let result = unsafe {
        server.dispatch(TRANSPORT_WAIT, |actual, _reply| {
            called = true;
            assert_eq!(actual.argv[2], "callback-error");
            Err(invalid("actual callback refused"))
        })
    };
    assert!(called && result.is_err());
    sender.join().unwrap();
    let (server, client) = pair().unwrap();
    let (mut local, remote) = UnixStream::pair().unwrap();
    control::no_sigpipe(local.as_fd()).unwrap();
    control::send(&client.control, Some(remote.as_fd())).unwrap();
    drop(remote);
    let sender = thread::spawn(move || {
        for byte in [0, 0, 0, 80] {
            if local.write_all(&[byte]).is_err() {
                break;
            }
            thread::sleep(Duration::from_millis(60));
        }
    });
    let start = std::time::Instant::now();
    let result = incoming(&server).read(Duration::from_millis(100));
    assert!(result.is_err());
    assert!(start.elapsed() < Duration::from_secs(2));
    sender.join().unwrap();
}

#[test]
fn failed_endpoint_adoption_releases_both_sender_copies() {
    for mode in 0..3 {
        let (server, client) = pair().unwrap();
        let client = Arc::new(client);
        let descriptors = || std::fs::read_dir("/dev/fd").unwrap().count();
        let before = descriptors();
        let sender_client = Arc::clone(&client);
        let sender = thread::spawn(move || {
            let start = std::time::Instant::now();
            assert!(sender_client
                .submit(&request("failed-adoption"), Duration::from_millis(100))
                .is_err());
            assert!(start.elapsed() < Duration::from_secs(2));
        });
        let mut received = incoming(&server);
        match mode {
            0 => drop(received), // receiver closes before acknowledgement
            1 => {
                received.socket.write_all(b"WRONGACK").unwrap();
                drop(received);
            }
            _ => {
                for byte in ADOPTED {
                    if received.socket.write_all(&[byte]).is_err() {
                        break;
                    }
                    thread::sleep(Duration::from_millis(40));
                }
                drop(received);
            }
        }
        sender.join().unwrap();
        assert_eq!(
            descriptors(),
            before,
            "failed endpoint handoff retained an FD"
        );
    }
}
