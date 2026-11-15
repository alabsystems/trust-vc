// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bounded syntax partition of already-authenticated original source bytes.

use rustc_lexer::{DocStyle, FrontmatterAllowed, LiteralKind, TokenKind};

const TOKENS: usize = 4096;
const DEPTH: usize = 64;

#[derive(Clone, Copy)]
pub(super) enum Kind {
    Attribute,
    Document,
}

pub(super) struct Part {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) kind: Kind,
}

struct Token<'s> {
    kind: TokenKind,
    text: &'s str,
}
struct Scan {
    remaining: usize,
}

impl Scan {
    fn tokens<'s>(&mut self, source: &'s str) -> Result<Vec<Token<'s>>, &'static str> {
        let mut tokens = Vec::new();
        let mut cursor = 0usize;
        for token in rustc_lexer::tokenize(source, FrontmatterAllowed::No) {
            self.remaining = self
                .remaining
                .checked_sub(1)
                .ok_or("the enum source prefix exceeds its token bound")?;
            if !valid(token.kind) {
                return Err("the enum source prefix contains an unrepresented lexical token");
            }
            let end = cursor
                .checked_add(token.len as usize)
                .ok_or("the enum source token range overflows")?;
            let text = source
                .get(cursor..end)
                .ok_or("the enum source token range is invalid")?;
            tokens.push(Token {
                kind: token.kind,
                text,
            });
            cursor = end;
        }
        if cursor != source.len() {
            return Err("the enum source scan did not cover its input");
        }
        Ok(tokens)
    }
}

fn valid(kind: TokenKind) -> bool {
    match kind {
        TokenKind::BlockComment { terminated, .. } => terminated,
        TokenKind::Literal { kind, .. } => match kind {
            LiteralKind::Int { empty_int, .. } => !empty_int,
            LiteralKind::Float { empty_exponent, .. } => !empty_exponent,
            LiteralKind::Char { terminated }
            | LiteralKind::Byte { terminated }
            | LiteralKind::Str { terminated }
            | LiteralKind::ByteStr { terminated }
            | LiteralKind::CStr { terminated } => terminated,
            LiteralKind::RawStr { n_hashes }
            | LiteralKind::RawByteStr { n_hashes }
            | LiteralKind::RawCStr { n_hashes } => n_hashes.is_some(),
        },
        TokenKind::Unknown
        | TokenKind::UnknownPrefix
        | TokenKind::UnknownPrefixLifetime
        | TokenKind::InvalidIdent
        | TokenKind::GuardedStrPrefix
        | TokenKind::Frontmatter { .. }
        | TokenKind::Eof => false,
        TokenKind::Lifetime { starts_with_number } => !starts_with_number,
        _ => true,
    }
}

fn trivia(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Whitespace
            | TokenKind::LineComment { doc_style: None }
            | TokenKind::BlockComment {
                doc_style: None,
                terminated: true
            }
    )
}

fn gap(scan: &mut Scan, source: &str) -> Result<(), &'static str> {
    if scan.tokens(source)?.iter().any(|token| !trivia(token.kind)) {
        return Err("the enum prefix has uncovered source syntax between attached attributes");
    }
    Ok(())
}

fn meta(tokens: &[&Token<'_>]) -> bool {
    let path_name = |kind| matches!(kind, TokenKind::Ident | TokenKind::RawIdent);
    if tokens.is_empty() || !path_name(tokens[0].kind) {
        return false;
    }
    let mut cursor = 1;
    while tokens
        .get(cursor)
        .is_some_and(|token| token.kind == TokenKind::Colon)
    {
        if tokens
            .get(cursor + 1)
            .is_none_or(|token| token.kind != TokenKind::Colon)
            || tokens
                .get(cursor + 2)
                .is_none_or(|token| !path_name(token.kind))
        {
            return false;
        }
        cursor += 3;
    }
    let Some(token) = tokens.get(cursor) else {
        return true;
    };
    if token.kind == TokenKind::Eq {
        return tokens.len() == cursor + 2
            && (matches!(tokens[cursor + 1].kind, TokenKind::Literal { .. })
                || matches!(tokens[cursor + 1].text, "true" | "false"));
    }
    if !matches!(
        token.kind,
        TokenKind::OpenParen | TokenKind::OpenBracket | TokenKind::OpenBrace
    ) {
        return false;
    }
    let mut depth = 0;
    for (index, token) in tokens.iter().enumerate().skip(cursor) {
        match token.kind {
            TokenKind::OpenParen | TokenKind::OpenBracket | TokenKind::OpenBrace => depth += 1,
            TokenKind::CloseParen | TokenKind::CloseBracket | TokenKind::CloseBrace => depth -= 1,
            _ => {}
        }
        if depth == 0 {
            return index + 1 == tokens.len();
        }
    }
    false
}

fn attribute(scan: &mut Scan, source: &str, kind: Kind) -> Result<(), &'static str> {
    let tokens = scan.tokens(source)?;
    if matches!(kind, Kind::Document)
        && tokens.len() == 1
        && matches!(
            tokens[0].kind,
            TokenKind::LineComment {
                doc_style: Some(DocStyle::Outer)
            } | TokenKind::BlockComment {
                doc_style: Some(DocStyle::Outer),
                terminated: true
            }
        )
    {
        return Ok(());
    }
    if tokens
        .first()
        .is_none_or(|token| token.kind != TokenKind::Pound)
        || tokens
            .last()
            .is_none_or(|token| token.kind != TokenKind::CloseBracket)
    {
        return Err("an enum prefix span is not one complete outer attribute");
    }
    let significant = tokens
        .iter()
        .filter(|token| !trivia(token.kind))
        .collect::<Vec<_>>();
    if significant.len() < 3 || significant[1].kind != TokenKind::OpenBracket {
        return Err("an enum prefix span is not an outer bracket attribute");
    }
    let mut stack = Vec::new();
    for (index, token) in significant.iter().enumerate().skip(1) {
        let close = match token.kind {
            TokenKind::OpenBracket => Some(TokenKind::CloseBracket),
            TokenKind::OpenParen => Some(TokenKind::CloseParen),
            TokenKind::OpenBrace => Some(TokenKind::CloseBrace),
            _ => None,
        };
        if let Some(close) = close {
            if stack.len() >= DEPTH {
                return Err("the enum source attribute exceeds its delimiter bound");
            }
            stack.push(close);
        } else if matches!(
            token.kind,
            TokenKind::CloseBracket | TokenKind::CloseParen | TokenKind::CloseBrace
        ) && stack.pop() != Some(token.kind)
        {
            return Err("the enum source attribute has unmatched delimiters");
        }
        if stack.is_empty() && index + 1 != significant.len() {
            return Err("an enum prefix span covers more than one attribute token group");
        }
        if matches!(
            token.kind,
            TokenKind::LineComment { doc_style: Some(_) }
                | TokenKind::BlockComment {
                    doc_style: Some(_),
                    ..
                }
        ) {
            return Err("an enum source attribute contains an unrepresented doc fragment");
        }
    }
    if !stack.is_empty() {
        return Err("the enum source attribute has an open delimiter");
    }
    if !meta(&significant[2..significant.len() - 1]) {
        return Err("the enum source prefix attribute grammar is not represented");
    }
    if matches!(kind, Kind::Document) {
        // Native Raw/Sugared is a re-emission detail. The original syntax can
        // be a doc comment (above) or the actual #[doc = string] form here.
        let string = significant.get(4).is_some_and(|token| {
            matches!(
                token.kind,
                TokenKind::Literal {
                    kind: LiteralKind::Str { terminated: true }
                        | LiteralKind::RawStr { n_hashes: Some(_) },
                    ..
                }
            )
        });
        if significant.len() != 6
            || significant[2].kind != TokenKind::Ident
            || significant[2].text != "doc"
            || significant[3].kind != TokenKind::Eq
            || !string
        {
            return Err("a native doc attribute does not cover original outer doc syntax");
        }
    }
    Ok(())
}

/// Each native source-prefix slot covers exactly one source attribute; gaps
/// contain only ordinary trivia. Callers pay the bounded byte work before
/// UTF-8 or lexer scans and keep the complete actual owner/slot inventory.
pub(super) fn partition(source: &str, parts: &[Part]) -> Result<(), &'static str> {
    let mut scan = Scan { remaining: TOKENS };
    let mut cursor = 0;
    for part in parts {
        if part.start < cursor || part.start >= part.end {
            return Err("the enum prefix repeats or overlaps source attributes");
        }
        let prefix = source
            .get(cursor..part.start)
            .ok_or("the enum prefix gap has invalid coordinates")?;
        let text = source
            .get(part.start..part.end)
            .ok_or("the enum source attribute has invalid coordinates")?;
        gap(&mut scan, prefix)?;
        attribute(&mut scan, text, part.kind)?;
        cursor = part.end;
    }
    gap(
        &mut scan,
        source
            .get(cursor..)
            .ok_or("the enum prefix tail is invalid")?,
    )
}

#[cfg(test)]
mod tests;
