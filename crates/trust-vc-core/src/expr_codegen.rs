//! Compile-time codegen: `syn::Expr` → `TrustVcExpr` builder `TokenStream`.
//!
//! Copyright 2026 Andrew Yates | Apache-2.0 | Author: Andrew Yates
//!
//! Generates runtime code constructing `TrustVcExpr` via `ir_builder`. Variable
//! types resolved at runtime via `lookup_var_type()`. Unsupported expressions
//! return `None` (fallback to string path).

use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::Parser;

fn support_root() -> syn::Path {
    crate::macro_support_root()
}

fn ir_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::ir }
}

fn ir_builder_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::ir_builder }
}

fn verify_macro_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::verify_macro }
}

fn extensional_eq_path() -> TokenStream {
    let support_root = support_root();
    quote! { #support_root::extensional_eq }
}

/// Generates a `TokenStream` constructing a `TrustVcExpr` from a `syn::Expr`.
/// Returns `None` for unsupported expression forms (fallback to string path).
pub fn expr_to_builder_tokens(expr: &syn::Expr) -> Option<TokenStream> {
    match expr {
        syn::Expr::Lit(lit) => lower_lit(lit),
        syn::Expr::Path(path) => lower_path(path),
        syn::Expr::Binary(bin) => lower_binary(bin),
        syn::Expr::Unary(un) => lower_unary(un),
        syn::Expr::Paren(paren) => expr_to_builder_tokens(&paren.expr),
        syn::Expr::Group(group) => expr_to_builder_tokens(&group.expr),
        syn::Expr::If(if_expr) => lower_if(if_expr),
        syn::Expr::Cast(cast) => lower_cast(cast),
        syn::Expr::MethodCall(method) => lower_method_call(method),
        syn::Expr::Call(call) => lower_call(call),
        syn::Expr::Block(block) => lower_block(block),
        syn::Expr::Macro(mac) => lower_macro(mac),
        syn::Expr::Tuple(tuple) if tuple.elems.is_empty() => {
            let ir_builder_path = ir_builder_path();
            Some(quote! { #ir_builder_path::unit_lit() })
        }
        // Unsupported expression types fall back to string path
        _ => None,
    }
}

/// Like `expr_to_builder_tokens`, but wraps output in `Option<TrustVcExpr>` so
/// runtime-failable `lookup_var_type` propagates via `?`. Fixes #2233.
pub fn expr_to_try_builder_tokens(expr: &syn::Expr) -> Option<TokenStream> {
    let inner = expr_to_builder_tokens(expr)?;
    let ir_path = ir_path();
    Some(quote! {
        (|| -> Option<#ir_path::TrustVcExpr> { Some(#inner) })()
    })
}

fn lower_lit(lit: &syn::ExprLit) -> Option<TokenStream> {
    let ir_path = ir_path();
    let ir_builder_path = ir_builder_path();
    match &lit.lit {
        syn::Lit::Bool(b) => {
            let val = b.value();
            Some(quote! { #ir_builder_path::bool_lit(#val) })
        }
        syn::Lit::Int(int_lit) => {
            let value: i128 = int_lit.base10_parse().ok()?;
            let suffix = int_lit.suffix();
            let ty_tokens = int_suffix_to_type(suffix);
            Some(quote! {
                #ir_builder_path::int_lit(#value, #ty_tokens)
            })
        }
        syn::Lit::Float(float_lit) => {
            let suffix = float_lit.suffix();
            let width = match suffix {
                "f32" => 32u32,
                "f64" => 64u32,
                _ => return None,
            };
            let value = integral_float_literal_value(float_lit)?;
            let from_ty = if i128::from(i32::MIN) <= value && value <= i128::from(i32::MAX) {
                quote! { #ir_path::TrustVcType::Int { width: 32 } }
            } else if i128::from(i64::MIN) <= value && value <= i128::from(i64::MAX) {
                quote! { #ir_path::TrustVcType::Int { width: 64 } }
            } else {
                return None;
            };
            let to_ty = quote! { #ir_path::TrustVcType::Float { width: #width } };
            Some(quote! {
                #ir_builder_path::cast(
                    #ir_builder_path::int_lit(#value, #from_ty),
                    #from_ty,
                    #to_ty,
                )
            })
        }
        _ => None,
    }
}

fn integral_float_literal_value(float_lit: &syn::LitFloat) -> Option<i128> {
    let raw = float_lit.base10_digits().replace('_', "");
    let (mantissa, exponent) = if let Some((mantissa, exponent)) = raw.split_once(['e', 'E']) {
        (mantissa, exponent.parse::<i32>().ok()?)
    } else {
        (raw.as_str(), 0)
    };
    let (whole, frac) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = format!("{whole}{frac}");
    let mut numerator = digits.parse::<i128>().ok()?;
    let scale = i32::try_from(frac.len()).ok()?.checked_sub(exponent)?;
    if scale <= 0 {
        let shift = u32::try_from(scale.checked_neg()?).ok()?;
        for _ in 0..shift {
            numerator = numerator.checked_mul(10)?;
        }
        return Some(numerator);
    }
    let scale = u32::try_from(scale).ok()?;
    let mut denominator = 1i128;
    for _ in 0..scale {
        denominator = denominator.checked_mul(10)?;
    }
    (numerator % denominator == 0).then_some(numerator / denominator)
}

fn int_suffix_to_type(suffix: &str) -> TokenStream {
    let ir_path = ir_path();
    // Delegates to type_name_to_trust_vc_type for known suffixes; unsuffixed → i32.
    type_name_to_trust_vc_type(suffix)
        .unwrap_or_else(|| quote! { #ir_path::TrustVcType::Int { width: 32 } })
}

fn lower_path(path: &syn::ExprPath) -> Option<TokenStream> {
    let ir_builder_path = ir_builder_path();
    let verify_macro_path = verify_macro_path();
    if path.qself.is_some() {
        return None;
    }

    let segments = &path.path.segments;

    if segments.len() == 1 {
        let name = segments[0].ident.to_string();
        match name.as_str() {
            "true" => return Some(quote! { #ir_builder_path::bool_lit(true) }),
            "false" => return Some(quote! { #ir_builder_path::bool_lit(false) }),
            _ => {}
        }
        // Variable: `?` propagates None to caller's Option context (#2233).
        Some(quote! {
            #ir_builder_path::var(
                #name,
                #verify_macro_path::lookup_var_type(#name)?,
            )
        })
    } else if segments.len() == 2 {
        // Handle T::MAX, T::MIN, T::BITS
        let type_name = segments[0].ident.to_string();
        let const_name = segments[1].ident.to_string();
        let ty_tokens = type_name_to_trust_vc_type(&type_name)?;
        match const_name.as_str() {
            "MAX" => Some(quote! { #ir_builder_path::int_max(#ty_tokens) }),
            "MIN" => Some(quote! { #ir_builder_path::int_min(#ty_tokens) }),
            "BITS" => Some(quote! { #ir_builder_path::int_bits(#ty_tokens) }),
            _ => None,
        }
    } else {
        None
    }
}

fn type_name_to_trust_vc_type(name: &str) -> Option<TokenStream> {
    let ir_path = ir_path();
    match name {
        "()" => Some(quote! { #ir_path::TrustVcType::Unit }),
        "bool" => Some(quote! { #ir_path::TrustVcType::Bool }),
        "i8" => Some(quote! { #ir_path::TrustVcType::Int { width: 8 } }),
        "i16" => Some(quote! { #ir_path::TrustVcType::Int { width: 16 } }),
        "i32" => Some(quote! { #ir_path::TrustVcType::Int { width: 32 } }),
        "i64" => Some(quote! { #ir_path::TrustVcType::Int { width: 64 } }),
        "i128" => Some(quote! { #ir_path::TrustVcType::Int { width: 128 } }),
        "u8" => Some(quote! { #ir_path::TrustVcType::Uint { width: 8 } }),
        "u16" => Some(quote! { #ir_path::TrustVcType::Uint { width: 16 } }),
        "u32" => Some(quote! { #ir_path::TrustVcType::Uint { width: 32 } }),
        "u64" => Some(quote! { #ir_path::TrustVcType::Uint { width: 64 } }),
        "u128" => Some(quote! { #ir_path::TrustVcType::Uint { width: 128 } }),
        "isize" => Some(quote! { #ir_path::TrustVcType::Int { width: #ir_path::pointer_width() } }),
        "usize" => {
            Some(quote! { #ir_path::TrustVcType::Uint { width: #ir_path::pointer_width() } })
        }
        "f32" => Some(quote! { #ir_path::TrustVcType::Float { width: 32 } }),
        "f64" => Some(quote! { #ir_path::TrustVcType::Float { width: 64 } }),
        "int" => Some(quote! { #ir_path::TrustVcType::MathInt }),
        "nat" => Some(quote! { #ir_path::TrustVcType::Nat }),
        _ => None,
    }
}

fn lower_binary(bin: &syn::ExprBinary) -> Option<TokenStream> {
    let ir_builder_path = ir_builder_path();
    let left = expr_to_builder_tokens(&bin.left)?;
    let right = expr_to_builder_tokens(&bin.right)?;

    match &bin.op {
        // Comparison operators
        syn::BinOp::Eq(_) => Some(quote! { #ir_builder_path::eq(#left, #right) }),
        syn::BinOp::Ne(_) => Some(quote! { #ir_builder_path::ne(#left, #right) }),
        syn::BinOp::Lt(_) => Some(quote! { #ir_builder_path::lt(#left, #right) }),
        syn::BinOp::Le(_) => Some(quote! { #ir_builder_path::le(#left, #right) }),
        syn::BinOp::Gt(_) => Some(quote! { #ir_builder_path::gt(#left, #right) }),
        syn::BinOp::Ge(_) => Some(quote! { #ir_builder_path::ge(#left, #right) }),

        // Logic operators
        syn::BinOp::And(_) => Some(quote! { #ir_builder_path::and(#left, #right) }),
        syn::BinOp::Or(_) => Some(quote! { #ir_builder_path::or(#left, #right) }),

        // Arithmetic operators: need result type, use i32 default
        syn::BinOp::Add(_)
        | syn::BinOp::Sub(_)
        | syn::BinOp::Mul(_)
        | syn::BinOp::Div(_)
        | syn::BinOp::Rem(_) => lower_binary_arith(&bin.op, &left, &right),

        // Bitwise/shift: use special_arith
        syn::BinOp::BitAnd(_)
        | syn::BinOp::BitOr(_)
        | syn::BinOp::BitXor(_)
        | syn::BinOp::Shl(_)
        | syn::BinOp::Shr(_) => lower_binary_bitwise(&bin.op, &left, &right),

        _ => None,
    }
}

fn lower_binary_arith(
    op: &syn::BinOp,
    left: &TokenStream,
    right: &TokenStream,
) -> Option<TokenStream> {
    let ir_path = ir_path();
    let ir_builder_path = ir_builder_path();
    let op_variant = match op {
        syn::BinOp::Add(_) => quote! { #ir_path::ArithOp::Add },
        syn::BinOp::Sub(_) => quote! { #ir_path::ArithOp::Sub },
        syn::BinOp::Mul(_) => quote! { #ir_path::ArithOp::Mul },
        syn::BinOp::Div(_) => quote! { #ir_path::ArithOp::Div },
        syn::BinOp::Rem(_) => quote! { #ir_path::ArithOp::Rem },
        _ => return None,
    };
    Some(quote! {
        #ir_builder_path::arith_inferred(#op_variant, #left, #right)
    })
}

fn lower_binary_bitwise(
    op: &syn::BinOp,
    left: &TokenStream,
    right: &TokenStream,
) -> Option<TokenStream> {
    let ir_path = ir_path();
    let ir_builder_path = ir_builder_path();
    let op_variant = match op {
        syn::BinOp::BitAnd(_) => quote! { #ir_path::SpecialArithOp::BitAnd },
        syn::BinOp::BitOr(_) => quote! { #ir_path::SpecialArithOp::BitOr },
        syn::BinOp::BitXor(_) => quote! { #ir_path::SpecialArithOp::BitXor },
        syn::BinOp::Shl(_) => quote! { #ir_path::SpecialArithOp::Shl },
        syn::BinOp::Shr(_) => quote! { #ir_path::SpecialArithOp::Shr },
        _ => return None,
    };
    Some(quote! {
        #ir_builder_path::special_arith_inferred(
            #op_variant, #left, #right,
        )
    })
}

fn lower_unary(un: &syn::ExprUnary) -> Option<TokenStream> {
    let ir_builder_path = ir_builder_path();
    let inner = expr_to_builder_tokens(&un.expr)?;
    match &un.op {
        syn::UnOp::Not(_) => Some(quote! { #ir_builder_path::not(#inner) }),
        syn::UnOp::Neg(_) => Some(quote! { #ir_builder_path::neg(#inner) }),
        _ => None,
    }
}

fn lower_if(if_expr: &syn::ExprIf) -> Option<TokenStream> {
    let ir_builder_path = ir_builder_path();
    let cond = expr_to_builder_tokens(&if_expr.cond)?;

    // Then branch: extract the expression from the block
    let then_expr = block_to_expr(&if_expr.then_branch)?;
    let then_tokens = expr_to_builder_tokens(&then_expr)?;

    // Else branch
    let else_tokens = match &if_expr.else_branch {
        Some((_, else_expr)) => expr_to_builder_tokens(else_expr)?,
        None => return None, // if without else not supported in typed path
    };

    Some(quote! {
        #ir_builder_path::ite_inferred(
            #cond,
            #then_tokens,
            #else_tokens,
        )
    })
}

fn lower_cast(cast: &syn::ExprCast) -> Option<TokenStream> {
    let ir_builder_path = ir_builder_path();
    let inner = expr_to_builder_tokens(&cast.expr)?;
    let to_ty = type_to_trust_vc_type(&cast.ty)?;
    Some(quote! {
        #ir_builder_path::cast_inferred(
            #inner,
            #to_ty,
        )
    })
}

fn lower_method_call(method: &syn::ExprMethodCall) -> Option<TokenStream> {
    let ir_path = ir_path();
    let ir_builder_path = ir_builder_path();
    let method_name = method.method.to_string();
    let (mode, op) = match method_name.as_str() {
        "wrapping_add" => (
            quote! { #ir_path::WrappingMode::Wrapping },
            quote! { #ir_path::ArithOp::Add },
        ),
        "wrapping_sub" => (
            quote! { #ir_path::WrappingMode::Wrapping },
            quote! { #ir_path::ArithOp::Sub },
        ),
        "wrapping_mul" => (
            quote! { #ir_path::WrappingMode::Wrapping },
            quote! { #ir_path::ArithOp::Mul },
        ),
        // Overflow-checked: BV result + overflow predicates, not Option<T> (#1785)
        "checked_add" => (
            quote! { #ir_path::WrappingMode::Checked },
            quote! { #ir_path::ArithOp::Add },
        ),
        "checked_sub" => (
            quote! { #ir_path::WrappingMode::Checked },
            quote! { #ir_path::ArithOp::Sub },
        ),
        "checked_mul" => (
            quote! { #ir_path::WrappingMode::Checked },
            quote! { #ir_path::ArithOp::Mul },
        ),
        "saturating_add" => (
            quote! { #ir_path::WrappingMode::Saturating },
            quote! { #ir_path::ArithOp::Add },
        ),
        "saturating_sub" => (
            quote! { #ir_path::WrappingMode::Saturating },
            quote! { #ir_path::ArithOp::Sub },
        ),
        "saturating_mul" => (
            quote! { #ir_path::WrappingMode::Saturating },
            quote! { #ir_path::ArithOp::Mul },
        ),
        _ => return None, // Unsupported method
    };

    if method.args.len() != 1 {
        return None;
    }

    let receiver = expr_to_builder_tokens(&method.receiver)?;
    let arg_expr = method.args.first()?;
    let arg = expr_to_builder_tokens(arg_expr)?;

    Some(quote! {
        #ir_builder_path::wrapping_arith_inferred(
            #mode, #op, #receiver, #arg,
        )
    })
}

fn lower_call(call: &syn::ExprCall) -> Option<TokenStream> {
    let ir_path = ir_path();
    let ir_builder_path = ir_builder_path();
    // Only handle simple function calls (no method calls, closures, etc.)
    let func_name = match &*call.func {
        syn::Expr::Path(path) if path.qself.is_none() => {
            let segments = &path.path.segments;
            if segments.len() == 1 {
                segments[0].ident.to_string()
            } else {
                return None;
            }
        }
        _ => return None,
    };

    let args: Option<Vec<TokenStream>> = call.args.iter().map(expr_to_builder_tokens).collect();
    let args = args?;
    let return_ty = if func_name == "__trust_vc_dt_size" {
        quote! { #ir_path::TrustVcType::MathInt }
    } else {
        quote! { #ir_path::TrustVcType::Bool }
    };

    Some(quote! {
        #ir_builder_path::fn_call(
            #func_name,
            vec![#(#args),*],
            #return_ty,
        )
    })
}

fn lower_macro(mac: &syn::ExprMacro) -> Option<TokenStream> {
    let extensional_eq_path = extensional_eq_path();
    let helper = match mac.mac.path.segments.last()?.ident.to_string().as_str() {
        "ext_eq" => quote! { #extensional_eq_path::build_ext_eq_expr },
        "ext_ne" => quote! { #extensional_eq_path::build_ext_ne_expr },
        "strict_eq" | "equal" => quote! { #extensional_eq_path::build_strict_eq_expr },
        _ => return None,
    };

    let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
        .parse2(mac.mac.tokens.clone())
        .ok()?;
    let [lhs, rhs] = args.into_iter().collect::<Vec<_>>().try_into().ok()?;
    let lhs = expr_to_builder_tokens(&lhs)?;
    let rhs = expr_to_builder_tokens(&rhs)?;

    Some(quote! { #helper(#lhs, #rhs) })
}

fn lower_block(block: &syn::ExprBlock) -> Option<TokenStream> {
    let expr = block_to_expr(&block.block)?;
    expr_to_builder_tokens(&expr)
}

fn block_to_expr(block: &syn::Block) -> Option<syn::Expr> {
    if block.stmts.len() == 1 {
        if let Some(syn::Stmt::Expr(expr, _)) = block.stmts.first() {
            return Some(expr.clone());
        }
    }
    None
}

fn quantifier_trigger_tokens(body: &syn::Expr) -> Option<TokenStream> {
    let mut trigger_exprs = Vec::new();
    collect_trigger_exprs(body, &mut trigger_exprs);
    if trigger_exprs.is_empty() {
        return Some(quote! { None });
    }

    let groups = trigger_exprs
        .into_iter()
        .map(|expr| {
            let trigger = expr_to_builder_tokens(expr)?;
            Some(quote! { vec![#trigger] })
        })
        .collect::<Option<Vec<_>>>()?;

    Some(quote! { Some(vec![#(#groups),*]) })
}

fn collect_trigger_exprs<'a>(expr: &'a syn::Expr, out: &mut Vec<&'a syn::Expr>) {
    struct TriggerCollector<'a, 'out> {
        out: &'out mut Vec<&'a syn::Expr>,
    }

    impl<'ast> syn::visit::Visit<'ast> for TriggerCollector<'ast, '_> {
        fn visit_expr(&mut self, expr: &'ast syn::Expr) {
            if expr_has_trigger_attr(expr) {
                self.out.push(expr);
                return;
            }
            syn::visit::visit_expr(self, expr);
        }
    }

    syn::visit::Visit::visit_expr(&mut TriggerCollector { out }, expr);
}

fn expr_has_trigger_attr(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Binary(binary) => attrs_have_trigger(&binary.attrs),
        syn::Expr::Call(call) => attrs_have_trigger(&call.attrs),
        syn::Expr::Cast(cast) => attrs_have_trigger(&cast.attrs),
        syn::Expr::Field(field) => attrs_have_trigger(&field.attrs),
        syn::Expr::Group(group) => attrs_have_trigger(&group.attrs),
        syn::Expr::Index(index) => attrs_have_trigger(&index.attrs),
        syn::Expr::Lit(lit) => attrs_have_trigger(&lit.attrs),
        syn::Expr::MethodCall(method) => attrs_have_trigger(&method.attrs),
        syn::Expr::Paren(paren) => attrs_have_trigger(&paren.attrs),
        syn::Expr::Path(path) => attrs_have_trigger(&path.attrs),
        syn::Expr::Reference(reference) => attrs_have_trigger(&reference.attrs),
        syn::Expr::Unary(unary) => attrs_have_trigger(&unary.attrs),
        _ => false,
    }
}

fn attrs_have_trigger(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "trigger")
    })
}

/// Lowers a closure to quantifier builder tokens. `kind`: `"Forall"` or `"Exists"`.
/// Registers bound var types so `lookup_var_type` resolves correctly.
/// Returns `Option<TrustVcExpr>` tokens; `?` propagates, unreg always runs (#2233).
pub fn closure_to_quantifier_tokens(closure: &syn::ExprClosure, kind: &str) -> Option<TokenStream> {
    let support_root = support_root();
    let ir_path = ir_path();
    let ir_builder_path = ir_builder_path();
    let fn_name = match kind {
        "Forall" => quote! { #ir_builder_path::forall },
        "Exists" => quote! { #ir_builder_path::exists },
        _ => return None,
    };

    let mut bound_var_tokens = Vec::new();
    let mut var_names: Vec<String> = Vec::new();
    let mut var_ty_tokens: Vec<TokenStream> = Vec::new();
    for param in &closure.inputs {
        let pat_type = match param {
            syn::Pat::Type(pt) => pt,
            _ => return None,
        };
        let name = match &*pat_type.pat {
            syn::Pat::Ident(ident) => ident.ident.to_string(),
            _ => return None,
        };
        let ty_tokens = type_to_trust_vc_type(&pat_type.ty)?;
        bound_var_tokens.push(quote! { (#name.to_string(), #ty_tokens) });
        var_names.push(name);
        var_ty_tokens.push(ty_tokens);
    }

    let body_tokens = expr_to_builder_tokens(&closure.body)?;
    let trigger_tokens = quantifier_trigger_tokens(&closure.body)?;

    // Register bound var types so lookup_var_type resolves them correctly
    let reg: Vec<_> = var_names
        .iter()
        .zip(&var_ty_tokens)
        .map(|(n, ty)| {
            quote! {
                #support_root::register_quantifier_bound_var(#n.to_string(), #ty);
            }
        })
        .collect();
    let unreg: Vec<_> = var_names
        .iter()
        .map(|n| {
            quote! {
                #support_root::unregister_quantifier_bound_var(#n);
            }
        })
        .collect();

    Some(quote! {{
        #(#reg)*
        let __trust_vc_qresult: Option<#ir_path::TrustVcExpr> =
            (|| -> Option<#ir_path::TrustVcExpr> {
                let __trust_vc_qbody = #body_tokens;
                let __trust_vc_qtriggers = #trigger_tokens;
                Some(#fn_name(vec![#(#bound_var_tokens),*], __trust_vc_qbody, __trust_vc_qtriggers))
            })();
        #(#unreg)*
        __trust_vc_qresult
    }})
}

fn type_to_trust_vc_type(ty: &syn::Type) -> Option<TokenStream> {
    match ty {
        syn::Type::Tuple(tuple) if tuple.elems.is_empty() => {
            let ir_path = ir_path();
            Some(quote! { #ir_path::TrustVcType::Unit })
        }
        syn::Type::Path(type_path) if type_path.qself.is_none() => {
            let segments = &type_path.path.segments;
            if segments.len() == 1 {
                type_name_to_trust_vc_type(&segments[0].ident.to_string())
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "expr_codegen_runtime.rs"]
pub(crate) mod runtime;

#[cfg(test)]
#[path = "expr_codegen_tests.rs"]
mod tests;
