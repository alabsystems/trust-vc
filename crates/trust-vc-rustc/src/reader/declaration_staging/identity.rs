//! The actual loaded compiler image, distinct from the producer executable.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::ffi::CStr;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};

use super::rustc_driver;
use crate::declaration_alignment::source_bindings::PinnedFile;

pub(super) fn loaded_driver_path() -> Result<PathBuf, String> {
    let mut info = MaybeUninit::<libc::Dl_info>::uninit();
    // The address is the genuine imported compiler entry point. dladdr only
    // writes its output structure; inspect it after a successful lookup.
    let found = unsafe {
        libc::dladdr(
            rustc_driver::run_compiler as *const () as *const libc::c_void,
            info.as_mut_ptr(),
        )
    };
    if found == 0 {
        return Err("the loaded native compiler image could not be identified".into());
    }
    let info = unsafe { info.assume_init() };
    if info.dli_fname.is_null() {
        return Err("the loaded native compiler image has no path".into());
    }
    let filename = unsafe { CStr::from_ptr(info.dli_fname) }
        .to_str()
        .map_err(|e| e.to_string())?;
    let path = PathBuf::from(filename)
        .canonicalize()
        .map_err(|e| e.to_string())?;
    let expected = Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
        .join("lib")
        .canonicalize()
        .map_err(|e| e.to_string())?;
    if path.parent() != Some(expected.as_path())
        || !path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with("librustc_driver-") && name.ends_with(".dylib"))
    {
        return Err("the actual loaded compiler image is outside the baked native sysroot".into());
    }
    Ok(path)
}

pub(super) fn loaded_driver() -> Result<PinnedFile, String> {
    let path = loaded_driver_path()?;
    Ok(PinnedFile {
        sha256: super::inputs::digest(&path)?,
        path,
    })
}
