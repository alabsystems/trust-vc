// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

pub(super) fn parse_item_fn(source: &str) -> syn::ItemFn {
    syn::parse_str::<syn::ItemFn>(source).expect("should parse as ItemFn")
}

pub(super) fn inline_module_fn<'a>(
    parsed: &'a syn::File,
    module_name: &str,
    fn_name: &str,
) -> &'a syn::ItemFn {
    let item_mod = parsed
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Mod(item_mod) if item_mod.ident == module_name => Some(item_mod),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing inline module `{module_name}`"));
    item_mod
        .content
        .as_ref()
        .unwrap_or_else(|| panic!("module `{module_name}` should be inline"))
        .1
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(item_fn) if item_fn.sig.ident == fn_name => Some(item_fn),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing function `{fn_name}` in module `{module_name}`"))
}
