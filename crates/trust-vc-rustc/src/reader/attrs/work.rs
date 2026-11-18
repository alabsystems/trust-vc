//! Attribute work is structural data, never a parsed-policy/owner token.
//! Default parsing is unchanged. Only syntax actually dispatched to the
//! Verus parser is visited; ignored doc/foreign payloads are not censused.

use super::*;

fn spend(remaining: &mut usize, amount: usize) -> Result<(), String> {
    *remaining = remaining
        .checked_sub(amount)
        .ok_or("native attribute parsing exceeds the caller's shared work bound")?;
    Ok(())
}

// Mirror token_trees' exact grammar and stop point. The initial reference
// collection is real parser work even if its first token is unsupported.
// Children are visited only after an identifier consumes their delimiter.
fn tokens(stream: &TokenStream, remaining: &mut usize) -> Result<bool, String> {
    let mut actual = Vec::new();
    let mut input = stream.iter();
    loop {
        spend(remaining, 1)?;
        let Some(tree) = input.next() else {
            break;
        };
        // Pay the actual parser's reference copy before this mirror's push.
        spend(remaining, 1)?;
        actual.push(tree);
    }
    let mut index = 0;
    while index < actual.len() {
        spend(remaining, 1)?;
        let TokenTree::Token(token, _) = actual[index] else {
            return Ok(false);
        };
        match token.kind {
            TokenKind::Literal(literal) => {
                // Tree owns this exact text; the semantic result may copy it
                // once more (proof_note/custom_err). Price both before parse.
                spend(remaining, literal.symbol.as_str().len())?;
                spend(remaining, literal.symbol.as_str().len())?;
            }
            TokenKind::Ident(symbol, _) => {
                spend(remaining, symbol.as_str().len())?;
                spend(remaining, symbol.as_str().len())?;
                if let Some(TokenTree::Delimited(_, _, _, inner)) = actual.get(index + 1) {
                    index += 1;
                    if !tokens(inner, remaining)? {
                        return Ok(false);
                    }
                }
            }
            TokenKind::Comma => {}
            _ => return Ok(false),
        }
        index += 1;
    }
    Ok(true)
}

pub(super) fn parsing(attrs: &[Attribute], remaining: &mut usize) -> Result<(), String> {
    // One structural row for the pricing pass, one for the unchanged parser
    // and its item-level consumer. There is no maximum-size per-row tax.
    spend(remaining, attrs.len())?;
    for attr in attrs {
        spend(remaining, 1)?;
        let item = match attr {
            Attribute::Tool(item) => item,
            Attribute::DeriveHelper(item) if item.path.segments.len() == 1 => item,
            _ => continue,
        };
        spend(remaining, item.path.segments.len())?;
        let mut path = item.path.segments.iter().map(|part| part.as_str());
        let first = path.next();
        let second = path.next();
        let third = path.next();
        // The semantic parser borrows all path segments, but only these
        // dispatched paths inspect/copy a name or enter argument tokens.
        // A foreign path's large symbol/payload is not a byte census.
        match (first, second, third) {
            (Some("verus"), Some("internal"), None) => {
                spend(remaining, "verus::internal".len())?;
                if let AttrArgs::Delimited(delimited) = &item.args {
                    let _ = tokens(&delimited.tokens, remaining)?;
                }
            }
            (Some("verifier"), Some(keyword), None) => {
                spend(remaining, "verifier::".len())?;
                spend(remaining, keyword.len())?;
                if let AttrArgs::Delimited(delimited) = &item.args {
                    let _ = tokens(&delimited.tokens, remaining)?;
                }
            }
            (Some("verus"), Some(other), None) => {
                spend(remaining, "verus::".len())?;
                spend(remaining, other.len())?;
            }
            (Some("verifier"), None, None) => spend(remaining, "verifier".len())?,
            _ => {}
        }
    }
    Ok(())
}

/// Before the existing equality check, price its actual retained operands.
/// Strings/list elements retain positions; no hash/equality summary replaces
/// the comparison. No clone or parsed result is stored by this helper.
pub(crate) fn comparison(
    left: &[(VerusAttr, Span)],
    right: &[(VerusAttr, Span)],
    remaining: &mut usize,
) -> Result<(), String> {
    spend(remaining, 1)?;
    if left.len() != right.len() {
        return Ok(());
    }
    for ((left, left_span), (right, right_span)) in left.iter().zip(right) {
        spend(remaining, 1)?;
        // Distinct variants short-circuit equality before any payload walk.
        if std::mem::discriminant(left) != std::mem::discriminant(right) {
            break;
        }
        match (left, right) {
            (VerusAttr::WhenUsedAsSpec(a), VerusAttr::WhenUsedAsSpec(b))
            | (VerusAttr::OtherGhostBlock(a), VerusAttr::OtherGhostBlock(b))
            | (VerusAttr::ProofNote(a), VerusAttr::ProofNote(b))
            | (VerusAttr::CustomErr(a), VerusAttr::CustomErr(b))
            | (VerusAttr::Unknown(a), VerusAttr::Unknown(b)) => {
                if a.len() == b.len() {
                    spend(remaining, a.len())?;
                }
            }
            (VerusAttr::LetMarker(a), VerusAttr::LetMarker(b)) => {
                if a.len() == b.len() {
                    spend(remaining, a.len())?;
                }
            }
            (VerusAttr::Trigger(Some(a)), VerusAttr::Trigger(Some(b))) => {
                if a.len() == b.len() {
                    spend(remaining, a.len())?;
                }
            }
            _ => {}
        }
        if left != right || left_span != right_span {
            break;
        }
    }
    Ok(())
}

/// Price the exact formatting stream before allocating its owned String.
/// The writer retains no output bytes or status/capability. Debug escaping
/// and native names are measured through the same actual formatter used by
/// the subsequent error; no estimated flat payload allowance is introduced.
pub(crate) fn formatting(
    arguments: std::fmt::Arguments<'_>,
    remaining: &mut usize,
) -> Result<(), String> {
    struct Output<'a>(&'a mut usize);
    impl std::fmt::Write for Output<'_> {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            *self.0 = self
                .0
                .checked_sub(1)
                .and_then(|left| left.checked_sub(text.len()))
                .ok_or(std::fmt::Error)?;
            Ok(())
        }
    }
    std::fmt::write(&mut Output(remaining), arguments).map_err(|_| {
        "native attribute error formatting exceeds the caller's shared work bound".into()
    })
}
