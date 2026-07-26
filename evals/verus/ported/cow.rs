// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::borrow::Cow;

use trust_vc_types::View;

#[derive(Copy, Clone)]
pub struct NumWrapper {
    pub x: u64,
}

impl View for NumWrapper {
    type ViewTy = u64;

    fn view(&self) -> u64 {
        self.x
    }
}

#[trust_vc::ensures(Cow::Owned(NumWrapper { x }).view() == x)]
fn test_cow_basic(x: u64) {}

#[trust_vc::ensures(Cow::Borrowed(a).view() == a.view())]
fn test_cow_str(a: &str) {}
