// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_merge_contract::api_surface;

fn main() -> Result<(), api_surface::ApiSurfaceError> {
    let _ = api_surface::write_default_api_surface_fixtures()?;
    Ok(())
}
