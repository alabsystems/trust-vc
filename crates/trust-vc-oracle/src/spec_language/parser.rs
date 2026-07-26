// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::ast::*;

// ---------------------------------------------------------------------------
// SpecParser
// ---------------------------------------------------------------------------

/// Recursive-descent parser for the mini spec language.
///
/// Grammar (informal):
/// ```text
/// expr     = implies
/// implies  = or ("==>" or)*
/// or       = and ("||" and)*
/// and      = compare ("&&" compare)*
/// compare  = additive (("==" | "!=" | "<" | "<=" | ">" | ">=") additive)?
/// additive = mult (("+" | "-") mult)*
/// mult     = unary (("*" | "/" | "%") unary)*
/// unary    = "!" unary | "-" unary | postfix
/// postfix  = primary ("." IDENT | "[" expr "]")*
/// primary  = INT | BOOL | "old(" expr ")" | "if" expr "then" expr "else" expr
///          | QUANT IDENT ":" TYPE ("," IDENT ":" TYPE)* "::" expr
///          | IDENT "(" args ")" | IDENT | "(" expr ")"
/// ```
pub struct SpecParser;

/// Internal parser state: tracks position within the input string.
struct ParserState<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> ParserState<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    fn remaining(&self) -> &'a str {
        &self.input[self.pos..]
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.input.len() && self.input.as_bytes()[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    fn eat_str(&mut self, s: &str) -> bool {
        self.skip_whitespace();
        if self.remaining().starts_with(s) {
            self.pos += s.len();
            true
        } else {
            false
        }
    }

    /// Try to consume `s` only if the next non-ws content is exactly `s`
    /// and is NOT followed by an identifier character (prevents matching
    /// "if" inside "iff").
    fn eat_keyword(&mut self, kw: &str) -> bool {
        self.skip_whitespace();
        let rem = self.remaining();
        if let Some(after) = rem.strip_prefix(kw) {
            if after.is_empty() || !is_ident_char(after.as_bytes()[0]) {
                self.pos += kw.len();
                return true;
            }
        }
        false
    }

    fn err(&self, msg: impl Into<String>) -> ParseError {
        ParseError::new(msg, self.pos)
    }

    fn parse_ident(&mut self) -> Result<String, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        while self.pos < self.input.len() && is_ident_char(self.input.as_bytes()[self.pos]) {
            self.pos += 1;
        }
        if self.pos == start {
            return Err(self.err("expected identifier"));
        }
        Ok(self.input[start..self.pos].to_string())
    }

    fn parse_int(&mut self) -> Result<i64, ParseError> {
        self.skip_whitespace();
        let start = self.pos;
        if self.pos < self.input.len() && self.input.as_bytes()[self.pos] == b'-' {
            self.pos += 1;
        }
        while self.pos < self.input.len() && self.input.as_bytes()[self.pos].is_ascii_digit() {
            self.pos += 1;
        }
        if self.pos == start || (self.pos == start + 1 && self.input.as_bytes()[start] == b'-') {
            self.pos = start;
            return Err(self.err("expected integer literal"));
        }
        self.input[start..self.pos]
            .parse::<i64>()
            .map_err(|e| self.err(e.to_string()))
    }
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

impl SpecParser {
    /// Parse a spec expression from text.
    pub fn parse_expr(input: &str) -> Result<SpecExpr, ParseError> {
        let mut state = ParserState::new(input);
        let expr = Self::parse_implies(&mut state)?;
        state.skip_whitespace();
        if state.pos != state.input.len() {
            return Err(state.err(format!(
                "unexpected trailing content: `{}`",
                state.remaining()
            )));
        }
        Ok(expr)
    }

    /// Parse a spec clause keyword (requires/ensures/invariant/decreases) + expression.
    pub fn parse_clause(input: &str) -> Result<SpecClause, ParseError> {
        let mut state = ParserState::new(input);
        state.skip_whitespace();
        if state.eat_keyword("requires") {
            let expr = Self::parse_implies(&mut state)?;
            state.skip_whitespace();
            if state.pos != state.input.len() {
                return Err(state.err("trailing content after clause"));
            }
            return Ok(SpecClause::Requires(expr));
        }
        if state.eat_keyword("ensures") {
            let expr = Self::parse_implies(&mut state)?;
            state.skip_whitespace();
            if state.pos != state.input.len() {
                return Err(state.err("trailing content after clause"));
            }
            return Ok(SpecClause::Ensures(expr));
        }
        if state.eat_keyword("invariant") {
            let expr = Self::parse_implies(&mut state)?;
            state.skip_whitespace();
            if state.pos != state.input.len() {
                return Err(state.err("trailing content after clause"));
            }
            return Ok(SpecClause::Invariant(expr));
        }
        if state.eat_keyword("decreases") {
            let expr = Self::parse_implies(&mut state)?;
            state.skip_whitespace();
            if state.pos != state.input.len() {
                return Err(state.err("trailing content after clause"));
            }
            return Ok(SpecClause::Decreases(expr));
        }
        Err(state.err("expected `requires`, `ensures`, `invariant`, or `decreases`"))
    }

    /// Parse a complete function spec block.
    ///
    /// Format:
    /// ```text
    /// fn name(param1: Type1, param2: Type2) -> ReturnType
    ///   requires expr
    ///   ensures expr
    ///   ...
    /// ```
    pub fn parse_function_spec(input: &str) -> Result<FunctionSpec, ParseError> {
        let mut state = ParserState::new(input);

        // "fn"
        if !state.eat_keyword("fn") {
            return Err(state.err("expected `fn`"));
        }

        // function name
        let name = state.parse_ident()?;

        // parameter list
        if !state.eat_str("(") {
            return Err(state.err("expected `(`"));
        }
        let mut params = Vec::new();
        if !state.eat_str(")") {
            loop {
                let pname = state.parse_ident()?;
                if !state.eat_str(":") {
                    return Err(state.err("expected `:` after parameter name"));
                }
                let ptype = Self::parse_type_name(&mut state)?;
                params.push((pname, ptype));
                if state.eat_str(")") {
                    break;
                }
                if !state.eat_str(",") {
                    return Err(state.err("expected `,` or `)` in parameter list"));
                }
            }
        }

        // optional return type
        let return_type = if state.eat_str("->") {
            Some(Self::parse_type_name(&mut state)?)
        } else {
            None
        };

        // clauses
        let mut clauses = Vec::new();
        loop {
            state.skip_whitespace();
            if state.pos >= state.input.len() {
                break;
            }
            let clause_start = state.pos;
            if state.eat_keyword("requires") {
                let expr = Self::parse_implies(&mut state)?;
                clauses.push(SpecClause::Requires(expr));
            } else if state.eat_keyword("ensures") {
                let expr = Self::parse_implies(&mut state)?;
                clauses.push(SpecClause::Ensures(expr));
            } else if state.eat_keyword("invariant") {
                let expr = Self::parse_implies(&mut state)?;
                clauses.push(SpecClause::Invariant(expr));
            } else if state.eat_keyword("decreases") {
                let expr = Self::parse_implies(&mut state)?;
                clauses.push(SpecClause::Decreases(expr));
            } else {
                state.pos = clause_start;
                break;
            }
        }

        state.skip_whitespace();
        if state.pos != state.input.len() {
            return Err(state.err(format!(
                "unexpected trailing content: `{}`",
                state.remaining()
            )));
        }

        Ok(FunctionSpec {
            name,
            params,
            return_type,
            clauses,
        })
    }

    // -- Type name parsing (simple: reads until comma/paren/arrow/ws-keyword) --

    fn parse_type_name(state: &mut ParserState<'_>) -> Result<String, ParseError> {
        state.skip_whitespace();
        let start = state.pos;
        // Accept alphanumeric, `_`, `<`, `>`, `&`, `:`, and internal spaces
        // Stop at `,`, `)`, `->`, or clause keywords.
        let mut depth = 0i32;
        while state.pos < state.input.len() {
            let b = state.input.as_bytes()[state.pos];
            if b == b'<' {
                depth += 1;
                state.pos += 1;
            } else if b == b'>' {
                if depth == 0 {
                    break;
                }
                depth -= 1;
                state.pos += 1;
            } else if depth == 0
                && ((b == b',' || b == b')')
                    || state.remaining().starts_with("->")
                    || is_clause_keyword(state.remaining()))
            {
                break;
            } else {
                state.pos += 1;
            }
        }
        let raw = state.input[start..state.pos].trim();
        if raw.is_empty() {
            return Err(state.err("expected type name"));
        }
        Ok(raw.to_string())
    }

    // -- Expression grammar (precedence climbing) --

    fn parse_implies(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        let mut lhs = Self::parse_or(state)?;
        while state.eat_str("==>") {
            let rhs = Self::parse_or(state)?;
            lhs = SpecExpr::BinOp(Box::new(lhs), BinOpKind::Implies, Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_or(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        let mut lhs = Self::parse_and(state)?;
        while state.eat_str("||") {
            let rhs = Self::parse_and(state)?;
            lhs = SpecExpr::BinOp(Box::new(lhs), BinOpKind::Or, Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_and(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        let mut lhs = Self::parse_compare(state)?;
        while state.eat_str("&&") {
            let rhs = Self::parse_compare(state)?;
            lhs = SpecExpr::BinOp(Box::new(lhs), BinOpKind::And, Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_compare(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        let lhs = Self::parse_additive(state)?;
        state.skip_whitespace();

        // Try two-char operators first to avoid prefix ambiguity.
        if state.eat_str("==") {
            // Make sure it wasn't part of "==>"
            if state.remaining().starts_with('>') {
                // Undo the "==" and bail — this is actually "==>".
                state.pos -= 2;
                return Ok(lhs);
            }
            let rhs = Self::parse_additive(state)?;
            return Ok(SpecExpr::BinOp(Box::new(lhs), BinOpKind::Eq, Box::new(rhs)));
        }
        if state.eat_str("!=") {
            let rhs = Self::parse_additive(state)?;
            return Ok(SpecExpr::BinOp(Box::new(lhs), BinOpKind::Ne, Box::new(rhs)));
        }
        if state.eat_str("<=") {
            let rhs = Self::parse_additive(state)?;
            return Ok(SpecExpr::BinOp(Box::new(lhs), BinOpKind::Le, Box::new(rhs)));
        }
        if state.eat_str(">=") {
            let rhs = Self::parse_additive(state)?;
            return Ok(SpecExpr::BinOp(Box::new(lhs), BinOpKind::Ge, Box::new(rhs)));
        }
        if state.eat_str("<") {
            let rhs = Self::parse_additive(state)?;
            return Ok(SpecExpr::BinOp(Box::new(lhs), BinOpKind::Lt, Box::new(rhs)));
        }
        if state.eat_str(">") {
            let rhs = Self::parse_additive(state)?;
            return Ok(SpecExpr::BinOp(Box::new(lhs), BinOpKind::Gt, Box::new(rhs)));
        }
        Ok(lhs)
    }

    fn parse_additive(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        let mut lhs = Self::parse_mult(state)?;
        loop {
            state.skip_whitespace();
            if state.remaining().starts_with('+') {
                state.pos += 1;
                let rhs = Self::parse_mult(state)?;
                lhs = SpecExpr::BinOp(Box::new(lhs), BinOpKind::Add, Box::new(rhs));
            } else if state.remaining().starts_with('-') {
                // Disambiguate: `-` after an expression is subtraction,
                // but a standalone `-` before a digit in unary context is
                // handled in parse_unary. At this level we always treat
                // it as subtraction.
                state.pos += 1;
                let rhs = Self::parse_mult(state)?;
                lhs = SpecExpr::BinOp(Box::new(lhs), BinOpKind::Sub, Box::new(rhs));
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn parse_mult(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        let mut lhs = Self::parse_unary(state)?;
        loop {
            state.skip_whitespace();
            if state.remaining().starts_with('*') {
                state.pos += 1;
                let rhs = Self::parse_unary(state)?;
                lhs = SpecExpr::BinOp(Box::new(lhs), BinOpKind::Mul, Box::new(rhs));
            } else if state.remaining().starts_with('/') {
                state.pos += 1;
                let rhs = Self::parse_unary(state)?;
                lhs = SpecExpr::BinOp(Box::new(lhs), BinOpKind::Div, Box::new(rhs));
            } else if state.remaining().starts_with('%') {
                state.pos += 1;
                let rhs = Self::parse_unary(state)?;
                lhs = SpecExpr::BinOp(Box::new(lhs), BinOpKind::Mod, Box::new(rhs));
            } else {
                break;
            }
        }
        Ok(lhs)
    }

    fn parse_unary(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        state.skip_whitespace();
        if state.remaining().starts_with('!') {
            state.pos += 1;
            let inner = Self::parse_unary(state)?;
            return Ok(SpecExpr::UnaryOp(UnaryOpKind::Not, Box::new(inner)));
        }
        // Negative sign: only if followed by a digit (to avoid ambiguity with subtraction).
        if state.remaining().starts_with('-')
            && state.remaining().len() > 1
            && state.remaining().as_bytes()[1].is_ascii_digit()
        {
            // Check if a numeric literal follows directly — parse as IntLit.
            let val = state.parse_int()?;
            return Ok(SpecExpr::IntLit(val));
        }
        Self::parse_postfix(state)
    }

    fn parse_postfix(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        let mut expr = Self::parse_primary(state)?;
        loop {
            state.skip_whitespace();
            if state.remaining().starts_with('.') {
                state.pos += 1;
                let field = state.parse_ident()?;
                expr = SpecExpr::FieldAccess(Box::new(expr), field);
            } else if state.remaining().starts_with('[') {
                state.pos += 1;
                let index = Self::parse_implies(state)?;
                if !state.eat_str("]") {
                    return Err(state.err("expected `]`"));
                }
                expr = SpecExpr::IndexAccess(Box::new(expr), Box::new(index));
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn parse_primary(state: &mut ParserState<'_>) -> Result<SpecExpr, ParseError> {
        state.skip_whitespace();
        if state.pos >= state.input.len() {
            return Err(state.err("unexpected end of input"));
        }

        let rem = state.remaining();

        // Boolean literals
        if state.eat_keyword("true") {
            return Ok(SpecExpr::BoolLit(true));
        }
        if state.eat_keyword("false") {
            return Ok(SpecExpr::BoolLit(false));
        }

        // old(expr)
        if state.eat_keyword("old") {
            if !state.eat_str("(") {
                return Err(state.err("expected `(` after `old`"));
            }
            let inner = Self::parse_implies(state)?;
            if !state.eat_str(")") {
                return Err(state.err("expected `)` after old expression"));
            }
            return Ok(SpecExpr::Old(Box::new(inner)));
        }

        // if-then-else
        if state.eat_keyword("if") {
            let cond = Self::parse_implies(state)?;
            if !state.eat_keyword("then") {
                return Err(state.err("expected `then`"));
            }
            let then_br = Self::parse_implies(state)?;
            if !state.eat_keyword("else") {
                return Err(state.err("expected `else`"));
            }
            let else_br = Self::parse_implies(state)?;
            return Ok(SpecExpr::IfThenElse(
                Box::new(cond),
                Box::new(then_br),
                Box::new(else_br),
            ));
        }

        // quantifiers: forall/exists var: Type, ... :: body
        if state.eat_keyword("forall") {
            return Self::parse_quantifier_body(state, QuantKind::Forall);
        }
        if state.eat_keyword("exists") {
            return Self::parse_quantifier_body(state, QuantKind::Exists);
        }

        // Integer literal
        if rem.as_bytes()[0].is_ascii_digit() {
            let val = state.parse_int()?;
            return Ok(SpecExpr::IntLit(val));
        }

        // Identifier or function call
        if is_ident_start(rem.as_bytes()[0]) {
            let ident = state.parse_ident()?;
            state.skip_whitespace();
            if state.remaining().starts_with('(') {
                state.pos += 1;
                let mut args = Vec::new();
                if !state.eat_str(")") {
                    loop {
                        let arg = Self::parse_implies(state)?;
                        args.push(arg);
                        if state.eat_str(")") {
                            break;
                        }
                        if !state.eat_str(",") {
                            return Err(state.err("expected `,` or `)` in argument list"));
                        }
                    }
                }
                return Ok(SpecExpr::FnCall(ident, args));
            }
            return Ok(SpecExpr::Variable(ident));
        }

        // Parenthesized expression
        if rem.starts_with('(') {
            state.pos += 1;
            let inner = Self::parse_implies(state)?;
            if !state.eat_str(")") {
                return Err(state.err("expected `)`"));
            }
            return Ok(inner);
        }

        Err(state.err(format!(
            "unexpected character: `{}`",
            rem.chars().next().unwrap_or('?')
        )))
    }

    fn parse_quantifier_body(
        state: &mut ParserState<'_>,
        kind: QuantKind,
    ) -> Result<SpecExpr, ParseError> {
        let mut bindings = Vec::new();
        loop {
            let name = state.parse_ident()?;
            if !state.eat_str(":") {
                return Err(state.err("expected `:` after quantifier variable"));
            }
            let ty = Self::parse_quantifier_type(state)?;
            bindings.push((name, ty));
            if state.eat_str("::") {
                break;
            }
            if !state.eat_str(",") {
                return Err(state.err("expected `,` or `::` in quantifier bindings"));
            }
        }
        let body = Self::parse_implies(state)?;
        Ok(SpecExpr::Quantifier(kind, bindings, Box::new(body)))
    }

    /// Parse a type in quantifier bindings: reads until `,` or `::`.
    fn parse_quantifier_type(state: &mut ParserState<'_>) -> Result<String, ParseError> {
        state.skip_whitespace();
        let start = state.pos;
        let mut depth = 0i32;
        while state.pos < state.input.len() {
            let rem = state.remaining();
            let b = rem.as_bytes()[0];
            if b == b'<' {
                depth += 1;
                state.pos += 1;
            } else if b == b'>' {
                if depth == 0 {
                    break;
                }
                depth -= 1;
                state.pos += 1;
            } else if depth == 0 && (b == b',' || rem.starts_with("::")) {
                break;
            } else {
                state.pos += 1;
            }
        }
        let raw = state.input[start..state.pos].trim();
        if raw.is_empty() {
            return Err(state.err("expected type in quantifier binding"));
        }
        Ok(raw.to_string())
    }
}

fn is_clause_keyword(s: &str) -> bool {
    for kw in &["requires", "ensures", "invariant", "decreases"] {
        if let Some(rest) = s.strip_prefix(kw) {
            if rest.is_empty() || !is_ident_char(rest.as_bytes()[0]) {
                return true;
            }
        }
    }
    false
}
