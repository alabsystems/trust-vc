//! Proc-macro support-root resolution for emitted verification paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use proc_macro2::{Ident, Span};
use proc_macro_crate::{crate_name as find_crate_name, FoundCrate};
use syn::{parse_quote, Path};

const FACADE_ROOTS: &[&str] = &["kani", "trust_mc"];

/// Returns the crate root that proc-macro expansions should use for hidden
/// verification support items.
///
/// Today this falls back to `::trust_vc_core` so existing trust_vc call sites keep
/// compiling unchanged. When the merged facade exists, the same emitted sites
/// can route through `::kani::__trust_vc_support` or `::trust_mc::__trust_vc_support`
/// without another cross-cutting sweep.
#[must_use]
pub fn macro_support_root() -> Path {
    macro_support_root_with(|package_name| find_crate_name(package_name).ok())
}

fn macro_support_root_with(mut lookup: impl FnMut(&str) -> Option<FoundCrate>) -> Path {
    for facade in FACADE_ROOTS {
        if let Some(path) = resolve_crate_path(facade, &mut lookup) {
            return parse_quote!(#path::__trust_vc_support);
        }
    }

    parse_quote!(::trust_vc_core)
}

fn resolve_crate_path(
    package_name: &str,
    lookup: &mut impl FnMut(&str) -> Option<FoundCrate>,
) -> Option<Path> {
    match lookup(package_name)? {
        FoundCrate::Itself => Some(parse_quote!(crate)),
        FoundCrate::Name(name) => {
            let ident = Ident::new(&name, Span::call_site());
            Some(parse_quote!(::#ident))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::macro_support_root_with;
    use proc_macro_crate::FoundCrate;
    use syn::Path;

    fn path_string(path: Path) -> String {
        quote::quote!(#path).to_string()
    }

    #[test]
    fn support_root_falls_back_to_trust_vc_core_without_facade() {
        let path = macro_support_root_with(|_| None);
        assert_eq!(path_string(path), ":: trust_vc_core");
    }

    #[test]
    fn support_root_prefers_kani_facade_when_present() {
        let path = macro_support_root_with(|name| match name {
            "kani" => Some(FoundCrate::Name("kani".to_string())),
            _ => None,
        });
        assert_eq!(path_string(path), ":: kani :: __trust_vc_support");
    }

    #[test]
    fn support_root_uses_local_facade_when_expanding_inside_itself() {
        let path = macro_support_root_with(|name| match name {
            "trust_mc" => Some(FoundCrate::Itself),
            _ => None,
        });
        assert_eq!(path_string(path), "crate :: __trust_vc_support");
    }
}
