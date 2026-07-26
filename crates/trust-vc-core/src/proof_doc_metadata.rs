// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proof-doc metadata transport for `#[proof]` functions.
//!
//! Emits and parses durable `#[doc = "trust_vc:..."]` attributes on proof
//! function items. `#2482` established the proof identity and tracked-param
//! channel; `#2593` extends the shared prefix contract with proof
//! requires/ensures/param metadata for static extraction.

pub(crate) const PROOF_DOC_MARKER: &str = "trust_vc:proof";
pub(crate) const TRACKED_PARAM_PREFIX: &str = "trust_vc:proof:tracked=";
pub(crate) const REQUIRES_DOC_PREFIX: &str = "trust_vc:requires:";
pub(crate) const ENSURES_DOC_PREFIX: &str = "trust_vc:ensures:";
pub(crate) const PARAM_DOC_PREFIX: &str = "trust_vc:param:";

/// Metadata extracted from proof-doc attributes on a function item.
#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProofDocMetadata {
    pub(crate) is_proof: bool,
    pub(crate) tracked_params: Vec<String>,
}

/// Extract proof-doc metadata from a slice of `syn::Attribute`.
///
/// Returns `Some(ProofDocMetadata)` if a `trust_vc:proof` doc marker is present,
/// `None` if no proof metadata is found. Returns `Err` if a tracked-param
/// marker is malformed (empty name after `tracked=`).
#[cfg(test)]
pub(crate) fn extract_proof_doc_metadata(
    attrs: &[syn::Attribute],
) -> crate::error::TrustVcResult<Option<ProofDocMetadata>> {
    let mut is_proof = false;
    let mut tracked_params = Vec::new();

    for attr in attrs {
        let value = match doc_value(attr) {
            Some(v) => v,
            None => continue,
        };

        if value == PROOF_DOC_MARKER {
            is_proof = true;
        } else if let Some(suffix) = value.strip_prefix(TRACKED_PARAM_PREFIX) {
            let name = suffix.trim();
            if name.is_empty() {
                return Err(crate::error::TrustVcError::from(
                    "malformed proof doc metadata: tracked= with empty parameter name".to_string(),
                ));
            }
            tracked_params.push(name.to_string());
        }
    }

    if is_proof {
        Ok(Some(ProofDocMetadata {
            is_proof: true,
            tracked_params,
        }))
    } else if !tracked_params.is_empty() {
        Err(crate::error::TrustVcError::from(
            "malformed proof doc metadata: tracked= markers without trust_vc:proof marker"
                .to_string(),
        ))
    } else {
        Ok(None)
    }
}

/// Extract the string value from a `#[doc = "..."]` attribute.
#[cfg(test)]
pub(crate) fn doc_value(attr: &syn::Attribute) -> Option<String> {
    if !attr.path().is_ident("doc") {
        return None;
    }
    if let syn::Meta::NameValue(nv) = &attr.meta {
        if let syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(s),
            ..
        }) = &nv.value
        {
            return Some(s.value());
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_attrs(code: &str) -> Vec<syn::Attribute> {
        let item: syn::ItemFn = syn::parse_str(code).expect("parse test function");
        item.attrs
    }

    #[test]
    fn test_proof_marker_present_no_tracked() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:proof"]
            fn foo() {}
            "#,
        );
        let result = extract_proof_doc_metadata(&attrs).unwrap();
        let meta = result.expect("should find proof metadata");
        assert!(meta.is_proof);
        assert!(meta.tracked_params.is_empty());
    }

    #[test]
    fn test_proof_marker_with_tracked_params() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:proof"]
            #[doc = "trust_vc:proof:tracked=token"]
            #[doc = "trust_vc:proof:tracked=perm"]
            fn foo() {}
            "#,
        );
        let result = extract_proof_doc_metadata(&attrs).unwrap();
        let meta = result.expect("should find proof metadata");
        assert!(meta.is_proof);
        assert_eq!(meta.tracked_params, vec!["token", "perm"]);
    }

    #[test]
    fn test_no_proof_markers_returns_none() {
        let attrs = parse_attrs(
            r#"
            #[doc = "some other doc"]
            #[allow(dead_code)]
            fn foo() {}
            "#,
        );
        let result = extract_proof_doc_metadata(&attrs).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn test_unrelated_doc_comments_ignored() {
        let attrs = parse_attrs(
            r#"
            /// This is a normal doc comment
            #[doc = "trust_vc:proof"]
            /// Another doc comment
            fn foo() {}
            "#,
        );
        let result = extract_proof_doc_metadata(&attrs).unwrap();
        let meta = result.expect("should find proof metadata");
        assert!(meta.is_proof);
        assert!(meta.tracked_params.is_empty());
    }

    #[test]
    fn test_empty_tracked_name_fails() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:proof"]
            #[doc = "trust_vc:proof:tracked="]
            fn foo() {}
            "#,
        );
        let msg = extract_proof_doc_metadata(&attrs)
            .expect_err("empty tracked name should fail")
            .to_string();
        assert!(msg.contains("empty parameter name"), "got: {msg}");
    }

    #[test]
    fn test_tracked_without_proof_marker_fails() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:proof:tracked=token"]
            fn foo() {}
            "#,
        );
        let msg = extract_proof_doc_metadata(&attrs)
            .expect_err("tracked without proof marker should fail")
            .to_string();
        assert!(msg.contains("without trust_vc:proof marker"), "got: {msg}");
    }

    #[test]
    fn test_no_attrs_returns_none() {
        let attrs = parse_attrs("fn foo() {}");
        let result = extract_proof_doc_metadata(&attrs).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn test_trust_vc_prefix_not_confused_with_proof() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:extern_spec:target=foo"]
            fn foo() {}
            "#,
        );
        let result = extract_proof_doc_metadata(&attrs).unwrap();
        assert!(result.is_none());
    }
}
