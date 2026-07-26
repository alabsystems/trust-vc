// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_merge_contract::fixtures;

fn main() -> Result<(), fixtures::FixtureError> {
    let representative = fixtures::write_default_representative_fixture()?;
    let counterexample = fixtures::write_default_representative_counterexample_fixture()?;
    let v4 = fixtures::write_default_v4_fixture()?;
    println!("wrote fixture: {}", representative.display());
    println!("wrote fixture: {}", counterexample.display());
    println!("wrote fixture: {}", v4.display());
    Ok(())
}
