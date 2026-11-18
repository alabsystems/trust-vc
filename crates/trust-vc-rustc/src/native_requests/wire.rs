// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
const VERSION: &[u8] = b"TVCARGV4";

pub(super) fn write_blob(to: &mut impl Write, bytes: &[u8]) -> io::Result<()> {
    let size = u32::try_from(bytes.len()).map_err(|_| invalid("oversize frame"))?;
    to.write_all(&size.to_be_bytes())?;
    to.write_all(bytes)
}

pub(super) fn read_blob(from: &mut impl Read, limit: usize) -> io::Result<Vec<u8>> {
    let mut size = [0; 4];
    from.read_exact(&mut size)?;
    let size = u32::from_be_bytes(size) as usize;
    if size > limit {
        return Err(invalid("oversize frame"));
    }
    let mut bytes = vec![0; size];
    from.read_exact(&mut bytes)?;
    Ok(bytes)
}

fn append(to: &mut Vec<u8>, bytes: &[u8]) -> io::Result<()> {
    if bytes.contains(&0)
        || to
            .len()
            .checked_add(4)
            .and_then(|n| n.checked_add(bytes.len()))
            .is_none_or(|n| n > MAX_REQUEST_BYTES)
    {
        return Err(invalid("invalid or oversize native request"));
    }
    write_blob(to, bytes)
}

pub(super) fn encode_request(request: &Request) -> io::Result<Vec<u8>> {
    if request.argv.is_empty()
        || request.argv.len() > MAX_ARGUMENTS
        || request.cargo.values.len() > MAX_ARGUMENTS
        || !request.cwd.is_absolute()
    {
        return Err(invalid("invalid native argv or cwd"));
    }
    let mut bytes = VERSION.to_vec();
    bytes.extend_from_slice(&(request.argv.len() as u32).to_be_bytes());
    for arg in &request.argv {
        append(&mut bytes, arg.as_bytes())?;
    }
    append(&mut bytes, request.cwd.as_os_str().as_bytes())?;
    for value in [&request.outputs.verdict_dir, &request.outputs.dump_vcir] {
        bytes.push(u8::from(value.is_some()));
        if let Some(path) = value {
            append(&mut bytes, path.as_os_str().as_bytes())?;
        }
    }
    bytes.push(u8::from(request.verusdoc.is_some()));
    if let Some(value) = &request.verusdoc {
        append(&mut bytes, value.as_bytes())?;
    }
    bytes.push(u8::from(request.macro_package_name.is_some()));
    if let Some(value) = &request.macro_package_name {
        append(&mut bytes, value.as_bytes())?;
    }
    bytes.extend_from_slice(&(request.cargo.values.len() as u32).to_be_bytes());
    for (key, value) in &request.cargo.values {
        append(&mut bytes, key.as_bytes())?;
        bytes.push(u8::from(value.is_some()));
        if let Some(value) = value {
            append(&mut bytes, value.as_bytes())?;
        }
    }
    if bytes.len() > MAX_REQUEST_BYTES {
        return Err(invalid("oversize native request"));
    }
    Ok(bytes)
}

fn field(cursor: &mut &[u8]) -> io::Result<OsString> {
    let size = take(cursor, 4)?;
    let size = u32::from_be_bytes(size.try_into().unwrap()) as usize;
    let bytes = take(cursor, size)?;
    if bytes.contains(&0) {
        return Err(invalid("NUL in native operand"));
    }
    Ok(OsString::from_vec(bytes.to_vec()))
}
fn take<'a>(cursor: &mut &'a [u8], size: usize) -> io::Result<&'a [u8]> {
    if size > cursor.len() {
        return Err(invalid("truncated native request"));
    }
    let (bytes, rest) = cursor.split_at(size);
    *cursor = rest;
    Ok(bytes)
}

pub(super) fn decode_request(mut bytes: &[u8]) -> io::Result<Request> {
    if bytes.len() > MAX_REQUEST_BYTES || take(&mut bytes, VERSION.len())? != VERSION {
        return Err(invalid("unknown native request format"));
    }
    let count = u32::from_be_bytes(take(&mut bytes, 4)?.try_into().unwrap()) as usize;
    if count == 0 || count > MAX_ARGUMENTS {
        return Err(invalid("invalid argument count"));
    }
    let mut argv = Vec::with_capacity(count);
    for _ in 0..count {
        argv.push(field(&mut bytes)?);
    }
    let cwd = PathBuf::from(field(&mut bytes)?);
    if !cwd.is_absolute() {
        return Err(invalid("relative native cwd"));
    }
    let mut output = || -> io::Result<Option<PathBuf>> {
        match take(&mut bytes, 1)?[0] {
            0 => Ok(None),
            1 => field(&mut bytes).map(|p| Some(PathBuf::from(p))),
            _ => Err(invalid("unknown output context")),
        }
    };
    let outputs = OutputContext {
        verdict_dir: output()?,
        dump_vcir: output()?,
    };
    let verusdoc = match take(&mut bytes, 1)?[0] {
        0 => None,
        1 => Some(field(&mut bytes)?),
        _ => return Err(invalid("unknown macro documentation context")),
    };
    let macro_package_name = match take(&mut bytes, 1)?[0] {
        0 => None,
        1 => Some(field(&mut bytes)?),
        _ => return Err(invalid("unknown macro package context")),
    };
    let count = u32::from_be_bytes(take(&mut bytes, 4)?.try_into().unwrap()) as usize;
    if count > MAX_ARGUMENTS {
        return Err(invalid("oversize Cargo environment"));
    }
    let mut values = std::collections::BTreeMap::new();
    for _ in 0..count {
        let key = field(&mut bytes)?
            .into_string()
            .map_err(|_| invalid("non-Unicode Cargo environment key"))?;
        let value = match take(&mut bytes, 1)?[0] {
            0 => None,
            1 => Some(field(&mut bytes)?),
            _ => return Err(invalid("unknown Cargo value presence")),
        };
        if values.insert(key, value).is_some() {
            return Err(invalid("duplicate Cargo environment key"));
        }
    }
    let cargo = CargoContext { values };
    if !bytes.is_empty() {
        return Err(invalid("trailing native request fields"));
    }
    Ok(Request {
        argv,
        cwd,
        outputs,
        verusdoc,
        cargo,
        macro_package_name,
    })
}
