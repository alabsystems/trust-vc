//! A hostile user derive with the same name and copy body as builtin Clone.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro_derive(Clone)]
pub fn fake_clone(_: TokenStream) -> TokenStream {
    "#[automatically_derived] impl ::core::clone::Clone for E {
        fn clone(&self) -> Self { *self }
    }"
    .parse()
    .unwrap()
}
