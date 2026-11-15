//! Typed AST for the D1a `state_machine!` body, parsed from the invocation's
//! token stream.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The grammar mirrors the pinned upstream parser
//! (`state_machines_macros/src/parse_token_stream.rs` and
//! `parse_transition.rs` at Verus `a40d57c7`). It parses more than D1a admits:
//! `assert`, `match`, `property!`, `birds_eye`, the sharding operations, sub-
//! updates and `require let` are all parsed here so that the well-formedness
//! pass can report upstream's own diagnostics first and the D1a admission pass
//! can then refuse them by name, instead of failing with a generic parse error.

use proc_macro2::{Span, TokenStream};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{braced, bracketed, parenthesized, token, Attribute, Expr, Ident, Pat, Token, Type};

/// A parsed `NAME <generics>? { .. }` machine body.
pub(crate) struct MachineAst {
    pub(crate) attrs: Vec<Attribute>,
    pub(crate) name: Ident,
    /// Raw generics, if written. `Err` carries upstream's non-type-param error.
    pub(crate) generics: Option<Result<syn::Generics, syn::Error>>,
    pub(crate) fields: Option<syn::FieldsNamed>,
    pub(crate) items: Vec<syn::Item>,
}

impl Parse for MachineAst {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let name: Ident = input.call(<Ident as syn::ext::IdentExt>::parse_any)?;
        let generics = if input.peek(Token![<]) {
            let mut generics: syn::Generics = input.parse()?;
            if input.peek(Token![where]) {
                generics.where_clause = Some(input.parse()?);
            }
            let non_type = generics
                .params
                .iter()
                .find(|param| !matches!(param, syn::GenericParam::Type(_)));
            Some(match non_type {
                Some(param) => Err(syn::Error::new(
                    param.span(),
                    "Only generic type parameters are supported for state machine",
                )),
                None => Ok(generics),
            })
        } else {
            None
        };
        let content;
        let _ = braced!(content in input);
        let mut fields = None;
        let mut items = Vec::new();
        while !content.is_empty() {
            if content.peek(Ident) && content.fork().parse::<Ident>().is_ok_and(|i| i == "fields") {
                let kw: Ident = content.parse()?;
                if fields.is_some() {
                    return Err(syn::Error::new(
                        kw.span(),
                        "Expected only one declaration of `fields` block",
                    ));
                }
                fields = Some(content.parse::<syn::FieldsNamed>()?);
            } else {
                items.push(content.parse::<syn::Item>()?);
            }
        }
        if !input.is_empty() {
            return Err(input.error("unexpected tokens after the state machine body"));
        }
        Ok(MachineAst {
            attrs,
            name,
            generics,
            fields,
            items,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum TransitionKind {
    Init,
    Transition,
    Readonly,
    Property,
}

#[derive(Clone)]
pub(crate) struct TransitionParam {
    pub(crate) name: Ident,
    pub(crate) ty: Type,
}

#[derive(Clone)]
pub(crate) struct TransitionAst {
    pub(crate) kind: TransitionKind,
    pub(crate) name: Ident,
    pub(crate) params: Vec<TransitionParam>,
    pub(crate) body: TStmt,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum LetKind {
    Normal,
    BirdsEye,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Refute {
    Exhaustive,
    Require,
    Assert,
}

#[derive(Clone)]
pub(crate) enum SubIdx {
    Field(Ident),
    Idx(Box<Expr>),
}

/// One sharding operation (`add`/`remove`/`have`/`deposit`/`withdraw`/`guard`).
/// Parsed only so it can be refused precisely.
#[derive(Clone)]
pub(crate) struct SpecialOp {
    pub(crate) op: &'static str,
    pub(crate) field: Ident,
    /// Expressions inside the element (for identifier validation).
    pub(crate) exprs: Vec<Expr>,
    pub(crate) pat: Option<Pat>,
}

impl SpecialOp {
    /// Upstream `SpecialOp::is_modifier`: everything but `have`/`guard`.
    pub(crate) fn is_modifier(&self) -> bool {
        !matches!(self.op, "have" | "guard")
    }
    pub(crate) fn only_in_readonly_or_property(&self) -> bool {
        self.op == "guard"
    }
}

/// The transition statement tree, in upstream's let-scoped shape: a `let`
/// wraps every statement that follows it in its block.
///
/// Every node keeps its source span. Not all of them are read today (D1a
/// reports refusals at the invocation line), so the spans are retained rather
/// than dropped: a span that was never recorded cannot be recovered later.
#[allow(dead_code)]
#[derive(Clone)]
pub(crate) enum TStmt {
    Block(Span, Vec<TStmt>),
    Let {
        span: Span,
        pat: Pat,
        ty: Option<Box<Type>>,
        kind: LetKind,
        refute: Refute,
        expr: Expr,
        body: Box<TStmt>,
    },
    If {
        span: Span,
        cond: Expr,
        thn: Box<TStmt>,
        els: Box<TStmt>,
    },
    Match {
        span: Span,
        expr: Expr,
        arms: Vec<(Pat, Option<Expr>, TStmt)>,
    },
    Require(Span, Expr),
    Assert(Span, Expr),
    Update(Span, Ident, Expr),
    SubUpdate(Span, Ident, Vec<SubIdx>, Expr),
    Init(Span, Ident, Expr),
    Special {
        span: Span,
        op: SpecialOp,
        body: Box<TStmt>,
    },
}

/// Parse a transition macro (`init!`, `transition!`, `readonly!`, `property!`).
pub(crate) fn parse_transition(mac: &syn::Macro) -> syn::Result<TransitionAst> {
    let kind = if mac.path.is_ident("init") {
        TransitionKind::Init
    } else if mac.path.is_ident("transition") {
        TransitionKind::Transition
    } else if mac.path.is_ident("readonly") {
        TransitionKind::Readonly
    } else if mac.path.is_ident("property") {
        TransitionKind::Property
    } else {
        return Err(syn::Error::new(
            mac.span(),
            "unrecognized macro for definiting a transition: expected `init!`, `transition!`, `readonly!`, or `property!`",
        ));
    };
    let inner: TransitionInner = syn::parse2(mac.tokens.clone())?;
    Ok(TransitionAst {
        kind,
        name: inner.name,
        params: inner.params,
        body: inner.body,
    })
}

struct TransitionInner {
    name: Ident,
    params: Vec<TransitionParam>,
    body: TStmt,
}

impl Parse for TransitionInner {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let name: Ident = input.call(<Ident as syn::ext::IdentExt>::parse_any)?;
        let params_stream;
        let _ = parenthesized!(params_stream in input);
        let mut params = Vec::new();
        while !params_stream.is_empty() {
            let name: Ident = params_stream.call(<Ident as syn::ext::IdentExt>::parse_any)?;
            let _: Token![:] = params_stream.parse()?;
            let ty: Type = params_stream.parse()?;
            params.push(TransitionParam { name, ty });
            if params_stream.is_empty() {
                break;
            }
            let _: Token![,] = params_stream.parse()?;
        }
        let body = parse_block(input)?;
        if !input.is_empty() {
            return Err(input.error("unexpected tokens after the transition body"));
        }
        Ok(TransitionInner { name, params, body })
    }
}

enum StmtOrLet {
    Stmt(TStmt),
    Let {
        span: Span,
        pat: Pat,
        ty: Option<Box<Type>>,
        kind: LetKind,
        refute: Refute,
        expr: Expr,
    },
    Special {
        span: Span,
        op: SpecialOp,
    },
}

fn parse_block(input: ParseStream) -> syn::Result<TStmt> {
    let content;
    let brace = braced!(content in input);
    let mut stmts = Vec::new();
    while !content.is_empty() {
        stmts.push(parse_stmt(&content)?);
    }
    Ok(stmts_to_block(brace.span.join(), stmts))
}

fn stmts_to_block(span: Span, stmts: Vec<StmtOrLet>) -> TStmt {
    let mut cur: Vec<TStmt> = Vec::new();
    for stmt in stmts.into_iter().rev() {
        match stmt {
            StmtOrLet::Stmt(stmt) => cur.push(stmt),
            StmtOrLet::Let {
                span,
                pat,
                ty,
                kind,
                refute,
                expr,
            } => {
                let body = TStmt::Block(span, cur.into_iter().rev().collect());
                cur = vec![TStmt::Let {
                    span,
                    pat,
                    ty,
                    kind,
                    refute,
                    expr,
                    body: Box::new(body),
                }];
            }
            StmtOrLet::Special { span, op } => {
                let body = TStmt::Block(span, cur.into_iter().rev().collect());
                cur = vec![TStmt::Special {
                    span,
                    op,
                    body: Box::new(body),
                }];
            }
        }
    }
    TStmt::Block(span, cur.into_iter().rev().collect())
}

fn peek_ident(input: ParseStream, word: &str) -> bool {
    input
        .fork()
        .call(<Ident as syn::ext::IdentExt>::parse_any)
        .is_ok_and(|ident| ident == word)
}

fn parse_stmt(input: ParseStream) -> syn::Result<StmtOrLet> {
    if input.peek(token::Brace) {
        return Ok(StmtOrLet::Stmt(parse_block(input)?));
    }
    if input.peek(Token![let]) {
        let let_token: Token![let] = input.parse()?;
        return parse_let(input, let_token.span, Refute::Exhaustive, LetKind::Normal);
    }
    if input.peek(Token![if]) {
        return Ok(StmtOrLet::Stmt(parse_conditional(input)?));
    }
    if input.peek(Token![match]) {
        return Ok(StmtOrLet::Stmt(parse_match(input)?));
    }
    let ident: Ident = match input.call(<Ident as syn::ext::IdentExt>::parse_any) {
        Ok(ident) => ident,
        Err(_) => return Err(input.error("expected transition statement (e.g., `update ...`)")),
    };
    let word = ident.to_string();
    match word.as_str() {
        "birds_eye" => {
            let _: Token![let] = input.parse()?;
            parse_let(input, ident.span(), Refute::Exhaustive, LetKind::BirdsEye)
        }
        "require" | "assert" => {
            let refute = if word == "require" {
                Refute::Require
            } else {
                Refute::Assert
            };
            if input.peek(Token![let]) {
                let _: Token![let] = input.parse()?;
                parse_let(input, ident.span(), refute, LetKind::Normal)
            } else if peek_ident(input, "birds_eye") {
                let _: Ident = input.call(<Ident as syn::ext::IdentExt>::parse_any)?;
                let _: Token![let] = input.parse()?;
                if refute == Refute::Require {
                    return Err(input.error("'require birds_eye let' is not allowed because 'require' statements should not be in the scope of a `birds_eye` let-binding; preconditions of an exchange cannot depend on such bindings"));
                }
                parse_let(input, ident.span(), refute, LetKind::BirdsEye)
            } else {
                let expr: Expr = input.parse()?;
                if refute == Refute::Assert && peek_ident(input, "by") {
                    let _: Ident = input.call(<Ident as syn::ext::IdentExt>::parse_any)?;
                    let _: syn::Block = input.parse()?;
                }
                let _: Token![;] = input.parse()?;
                let span = ident.span();
                Ok(StmtOrLet::Stmt(if refute == Refute::Require {
                    TStmt::Require(span, expr)
                } else {
                    TStmt::Assert(span, expr)
                }))
            }
        }
        "update" => {
            let field: Ident = input.call(<Ident as syn::ext::IdentExt>::parse_any)?;
            let mut subs = Vec::new();
            loop {
                if input.peek(Token![.]) {
                    let _: Token![.] = input.parse()?;
                    subs.push(SubIdx::Field(
                        input.call(<Ident as syn::ext::IdentExt>::parse_any)?,
                    ));
                } else if input.peek(token::Bracket) {
                    let content;
                    let _ = bracketed!(content in input);
                    subs.push(SubIdx::Idx(Box::new(content.parse()?)));
                } else {
                    break;
                }
            }
            let _: Token![=] = input.parse()?;
            let expr: Expr = input.parse()?;
            let _: Token![;] = input.parse()?;
            Ok(StmtOrLet::Stmt(if subs.is_empty() {
                TStmt::Update(ident.span(), field, expr)
            } else {
                TStmt::SubUpdate(ident.span(), field, subs, expr)
            }))
        }
        "init" => {
            let field: Ident = input.call(<Ident as syn::ext::IdentExt>::parse_any)?;
            let _: Token![=] = input.parse()?;
            let expr: Expr = input.parse()?;
            let _: Token![;] = input.parse()?;
            Ok(StmtOrLet::Stmt(TStmt::Init(ident.span(), field, expr)))
        }
        "have" | "add" | "remove" | "guard" | "deposit" | "withdraw" => {
            parse_special(input, ident, special_name(&word))
        }
        _ => Err(syn::Error::new(ident.span(), "expected transition stmt")),
    }
}

fn special_name(word: &str) -> &'static str {
    match word {
        "have" => "have",
        "add" => "add",
        "remove" => "remove",
        "guard" => "guard",
        "deposit" => "deposit",
        _ => "withdraw",
    }
}

fn parse_special(input: ParseStream, kw: Ident, op: &'static str) -> syn::Result<StmtOrLet> {
    let field: Ident = input.call(<Ident as syn::ext::IdentExt>::parse_any)?;
    match op {
        "have" | "guard" => {
            let _: Token![>=] = input.parse()?;
        }
        "deposit" => {
            let _: Token![+=] = input.parse()?;
        }
        "add" => {
            if input.peek(Token![+=]) {
                let _: Token![+=] = input.parse()?;
            } else if input.peek(token::Paren) {
                let content;
                let _ = parenthesized!(content in input);
                let _: TokenStream = content.parse()?;
                let _: Token![=] = input.parse()?;
            } else {
                return Err(input.error("expected += or union="));
            }
        }
        _ => {
            let _: Token![-=] = input.parse()?;
        }
    }
    let mut exprs = Vec::new();
    let mut pat = None;
    if input.peek(token::Brace) {
        let content;
        let _ = braced!(content in input);
        exprs.push(content.parse()?);
    } else if input.peek(token::Bracket) {
        let content;
        let _ = bracketed!(content in input);
        exprs.push(content.parse()?);
        let _: Token![=>] = content.parse()?;
        if content.peek(Token![let]) {
            let _: Token![let] = content.parse()?;
            pat = Some(Pat::parse_single(&content)?);
        } else {
            exprs.push(content.parse()?);
        }
    } else if peek_ident(input, "Some") {
        let _: Ident = input.parse()?;
        let content;
        let _ = parenthesized!(content in input);
        if content.peek(Token![let]) {
            let _: Token![let] = content.parse()?;
            pat = Some(Pat::parse_single(&content)?);
        } else {
            exprs.push(content.parse()?);
        }
    } else if peek_ident(input, "set") {
        let _: Ident = input.parse()?;
        let content;
        let _ = braced!(content in input);
        exprs.push(content.parse()?);
    } else if input.peek(syn::LitBool) {
        let _: syn::LitBool = input.parse()?;
    } else if input.peek(token::Paren) {
        let content;
        let _ = parenthesized!(content in input);
        exprs.push(content.parse()?);
    } else {
        return Err(input.error(format!("malformed {op} statement")));
    }
    if peek_ident(input, "by") {
        let _: Ident = input.parse()?;
        let _: syn::Block = input.parse()?;
    }
    let _: Token![;] = input.parse()?;
    let op = SpecialOp {
        op,
        field,
        exprs,
        pat,
    };
    Ok(StmtOrLet::Special {
        span: kw.span(),
        op,
    })
}

fn parse_conditional(input: ParseStream) -> syn::Result<TStmt> {
    let if_token: Token![if] = input.parse()?;
    let cond = input.call(Expr::parse_without_eager_brace)?;
    let thn = parse_block(input)?;
    let els = if input.peek(Token![else]) {
        let _: Token![else] = input.parse()?;
        if input.peek(Token![if]) {
            parse_conditional(input)?
        } else if input.peek(token::Brace) {
            parse_block(input)?
        } else {
            return Err(input.error("expected `if` or `{` after `else`"));
        }
    } else {
        TStmt::Block(if_token.span, Vec::new())
    };
    error_on_if_let(&cond)?;
    Ok(TStmt::If {
        span: if_token.span,
        cond,
        thn: Box::new(thn),
        els: Box::new(els),
    })
}

fn error_on_if_let(cond: &Expr) -> syn::Result<()> {
    struct IfLet(Option<Span>);
    impl<'ast> syn::visit::Visit<'ast> for IfLet {
        fn visit_expr_block(&mut self, _node: &'ast syn::ExprBlock) {}
        fn visit_expr_let(&mut self, node: &'ast syn::ExprLet) {
            self.0.get_or_insert(node.let_token.span);
        }
    }
    let mut visitor = IfLet(None);
    syn::visit::Visit::visit_expr(&mut visitor, cond);
    match visitor.0 {
        Some(span) => Err(syn::Error::new(
            span,
            "transition definitions do not support if-let conditionals (try using a 'match' statement instead)",
        )),
        None => Ok(()),
    }
}

fn parse_match(input: ParseStream) -> syn::Result<TStmt> {
    let match_token: Token![match] = input.parse()?;
    let expr = input.call(Expr::parse_without_eager_brace)?;
    let content;
    let _ = braced!(content in input);
    let mut arms = Vec::new();
    while !content.is_empty() {
        let pat = Pat::parse_multi_with_leading_vert(&content)?;
        let guard = if content.peek(Token![if]) {
            let _: Token![if] = content.parse()?;
            Some(content.parse::<Expr>()?)
        } else {
            None
        };
        let _: Token![=>] = content.parse()?;
        let body = parse_block(&content)?;
        if content.peek(Token![,]) {
            let _: Token![,] = content.parse()?;
        }
        arms.push((pat, guard, body));
    }
    Ok(TStmt::Match {
        span: match_token.span,
        expr,
        arms,
    })
}

fn parse_let(
    input: ParseStream,
    span: Span,
    refute: Refute,
    kind: LetKind,
) -> syn::Result<StmtOrLet> {
    let pat = Pat::parse_single(input)?;
    if let Pat::Ident(pat_ident) = &pat {
        if pat_ident.ident == "birds_eye" {
            return Err(syn::Error::new(
                pat.span(),
                "keywords in the wrong order: use `birds_eye let` instead",
            ));
        }
    }
    let ty = if input.peek(Token![:]) {
        let _: Token![:] = input.parse()?;
        Some(Box::new(input.parse::<Type>()?))
    } else {
        None
    };
    let _: Token![=] = input.parse()?;
    let expr: Expr = input.parse()?;
    let _: Token![;] = input.parse()?;
    Ok(StmtOrLet::Let {
        span,
        pat,
        ty,
        kind,
        refute,
        expr,
    })
}
