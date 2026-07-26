//! Clause parsing for `#[decreases(...)]` attributes.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracts measure expressions, `when` conditions, and `via` function
//! references from the attribute token stream.

use proc_macro2::TokenStream;

/// Parsed decreases clause with optional when/via/mutual_with.
pub(super) struct DecreasesClause {
    /// The measure expression(s)
    pub measures: TokenStream,
    /// Optional when condition
    pub when_condition: Option<TokenStream>,
    /// Optional via function name
    pub via_fn: Option<TokenStream>,
    /// Mutual recursion peer function names
    pub mutual_peers: Vec<String>,
}

/// Parses decreases attribute tokens to extract measures, when, via, and mutual_with clauses.
///
/// Syntax: `measure1, measure2, ..., when = condition, via = fn_name, mutual_with(peer1, peer2)`
pub(super) fn parse_decreases_clauses(tokens: TokenStream) -> DecreasesClause {
    use proc_macro2::TokenTree;

    let mut measures = TokenStream::new();
    let mut when_condition: Option<TokenStream> = None;
    let mut via_fn: Option<TokenStream> = None;
    let mut mutual_peers: Vec<String> = Vec::new();

    let mut iter = tokens.into_iter().peekable();
    let mut in_when = false;
    let mut in_via = false;
    let mut when_tokens = TokenStream::new();
    let mut via_tokens = TokenStream::new();

    while let Some(token) = iter.next() {
        match &token {
            TokenTree::Ident(ident) if ident == "when" => {
                if in_via {
                    via_tokens.extend(std::iter::once(token));
                    continue;
                }
                // Consume the '=' after 'when'
                if let Some(TokenTree::Punct(p)) = iter.peek() {
                    if p.as_char() == '=' {
                        iter.next(); // consume '='
                        in_when = true;
                        in_via = false;
                        continue;
                    }
                }
                // Not followed by '=', treat as part of measures
                if !in_when && !in_via {
                    measures.extend(std::iter::once(token));
                }
            }
            TokenTree::Ident(ident) if ident == "mutual_with" => {
                // Parse `mutual_with(fn1, fn2, ...)` — peer names in group parens
                if let Some(TokenTree::Group(group)) = iter.peek() {
                    if group.delimiter() == proc_macro2::Delimiter::Parenthesis {
                        let group = match iter.next() {
                            Some(TokenTree::Group(g)) => g,
                            _ => unreachable!(),
                        };
                        for tt in group.stream() {
                            if let TokenTree::Ident(peer) = tt {
                                mutual_peers.push(peer.to_string());
                            }
                            // Skip commas and whitespace
                        }
                        // Save any pending when/via tokens
                        if in_when && !when_tokens.is_empty() {
                            when_condition = Some(when_tokens.clone());
                            when_tokens = TokenStream::new();
                            in_when = false;
                        }
                        if in_via && !via_tokens.is_empty() {
                            via_fn = Some(via_tokens.clone());
                            via_tokens = TokenStream::new();
                            in_via = false;
                        }
                        continue;
                    }
                }
                // Not followed by parens — treat as regular identifier
                if in_when {
                    when_tokens.extend(std::iter::once(token));
                } else if in_via {
                    via_tokens.extend(std::iter::once(token));
                } else {
                    measures.extend(std::iter::once(token));
                }
            }
            TokenTree::Ident(ident) if ident == "via" => {
                // Consume the '=' after 'via'
                if let Some(TokenTree::Punct(p)) = iter.peek() {
                    if p.as_char() == '=' {
                        iter.next(); // consume '='
                                     // Save any pending when tokens before transitioning to via.
                                     // Handles `when = cond via = fn` (no comma separator). (#1739)
                        if in_when && !when_tokens.is_empty() {
                            when_condition = Some(when_tokens.clone());
                            when_tokens = TokenStream::new();
                        }
                        in_via = true;
                        in_when = false;
                        continue;
                    }
                }
                // "via" not followed by '=' — treat as identifier in context
                if in_when {
                    when_tokens.extend(std::iter::once(token));
                } else if in_via {
                    via_tokens.extend(std::iter::once(token));
                } else {
                    measures.extend(std::iter::once(token));
                }
            }
            TokenTree::Punct(p) if p.as_char() == ',' => {
                // Comma after via_fn name - skip it
                if in_via {
                    if !via_tokens.is_empty() {
                        via_fn = Some(via_tokens.clone());
                        via_tokens = TokenStream::new();
                    }
                    in_via = false;
                    continue;
                }
                // Comma in when clause
                if in_when {
                    // Check if next token is 'via' - if so, end when clause
                    if let Some(TokenTree::Ident(next_ident)) = iter.peek() {
                        if next_ident == "via" {
                            when_condition = Some(when_tokens.clone());
                            when_tokens = TokenStream::new();
                            in_when = false;
                            continue;
                        }
                    }
                    // Otherwise, include comma in when tokens
                    when_tokens.extend(std::iter::once(token));
                } else {
                    // Comma in measures
                    measures.extend(std::iter::once(token));
                }
            }
            _ => {
                if in_when {
                    when_tokens.extend(std::iter::once(token));
                } else if in_via {
                    via_tokens.extend(std::iter::once(token));
                } else if !in_via {
                    measures.extend(std::iter::once(token));
                }
            }
        }
    }

    // Save any remaining when tokens
    if in_when && !when_tokens.is_empty() {
        when_condition = Some(when_tokens);
    }
    if in_via && !via_tokens.is_empty() {
        via_fn = Some(via_tokens);
    }

    DecreasesClause {
        measures,
        when_condition,
        via_fn,
        mutual_peers,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;
    use syn::parse::Parser;

    fn normalize_tokens(tokens: &TokenStream) -> String {
        tokens
            .to_string()
            .chars()
            .filter(|ch| !ch.is_whitespace())
            .collect()
    }

    fn normalize_optional_tokens(tokens: &Option<TokenStream>) -> Option<String> {
        tokens.as_ref().map(normalize_tokens)
    }

    fn parse_measure_exprs(tokens: &TokenStream) -> Vec<String> {
        let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
        parser
            .parse2(tokens.clone())
            .expect("measures should stay parseable")
            .iter()
            .map(|expr| normalize_tokens(&quote!(#expr)))
            .collect()
    }

    #[test]
    fn test_parse_decreases_clauses_extracts_when_and_via() {
        let clause = parse_decreases_clauses(quote!(n, when = n > 0, via = proof_fn));

        assert_eq!(parse_measure_exprs(&clause.measures), vec!["n"]);
        assert_eq!(
            normalize_optional_tokens(&clause.when_condition).as_deref(),
            Some("n>0")
        );
        assert_eq!(
            normalize_optional_tokens(&clause.via_fn).as_deref(),
            Some("proof_fn")
        );
        assert!(clause.mutual_peers.is_empty());
    }

    #[test]
    fn test_parse_decreases_clauses_transitions_from_when_to_via_without_comma() {
        let clause = parse_decreases_clauses(quote!(n, when = n > 0 via = proof_fn));

        assert_eq!(parse_measure_exprs(&clause.measures), vec!["n"]);
        assert_eq!(
            normalize_optional_tokens(&clause.when_condition).as_deref(),
            Some("n>0")
        );
        assert_eq!(
            normalize_optional_tokens(&clause.via_fn).as_deref(),
            Some("proof_fn")
        );
    }

    #[test]
    fn test_parse_decreases_clauses_preserves_commas_inside_when_condition() {
        let clause = parse_decreases_clauses(quote!(n, when = within_bounds(a, b), via = proof_fn));

        assert_eq!(parse_measure_exprs(&clause.measures), vec!["n"]);
        assert_eq!(
            normalize_optional_tokens(&clause.when_condition).as_deref(),
            Some("within_bounds(a,b)")
        );
        assert_eq!(
            normalize_optional_tokens(&clause.via_fn).as_deref(),
            Some("proof_fn")
        );
    }

    #[test]
    fn test_parse_decreases_clauses_collects_mutual_peers_without_polluting_measures() {
        let clause = parse_decreases_clauses(quote!(
            m,
            n,
            via = lexicographic_proof,
            mutual_with(peer_a, peer_b)
        ));

        assert_eq!(parse_measure_exprs(&clause.measures), vec!["m", "n"]);
        assert_eq!(
            normalize_optional_tokens(&clause.via_fn).as_deref(),
            Some("lexicographic_proof")
        );
        assert_eq!(clause.mutual_peers, vec!["peer_a", "peer_b"]);
    }

    #[test]
    fn test_parse_decreases_clauses_treats_when_without_equals_as_measure_expression() {
        let clause = parse_decreases_clauses(quote!(n, when(flag)));

        assert_eq!(
            parse_measure_exprs(&clause.measures),
            vec!["n", "when(flag)"]
        );
        assert!(clause.when_condition.is_none());
        assert!(clause.via_fn.is_none());
        assert!(clause.mutual_peers.is_empty());
    }
}
