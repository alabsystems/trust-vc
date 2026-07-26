//! End-to-end verification module for trust_vc.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module provides the entry point for standalone trust_vc verification,
//! bridging the gap between proc-macro output and ay SMT solving.
//!
//! # Architecture
//!
//! ```text
//! User Code + Attributes
//!         |
//!         v
//! Proc Macros (expand to markers)
//!         |
//!         v
//! Verification Harness (this module)
//!         |
//!         v
//! VerificationContext::verify()
//!         |
//!         v
//! VerifyResult
//! ```
//!
//! # Integration Paths
//!
//! 1. **Direct API**: Build VerificationContext programmatically
//! 2. **Marker Parsing**: Extract from compiled code (future)
//! 3. **trust_mc Integration**: trust_mc calls trust_vc's encoder
//!
//! # Usage Example
//!
//! ```no_run
//! use trust_vc_core::verify::{Verifier, Proof};
//!
//! // Define a proof
//! let proof = Proof::new("identity")
//!     .with_variable("x", "i32")
//!     .with_assertion("x + 0 == x");
//!
//! // Run verification
//! let result = Verifier::verify(&proof);
//! assert!(result.is_verified());
//! ```

use crate::error::{TrustVcError, TrustVcResult};
use crate::ir::TrustVcType;
use crate::vc::{ProofObligation, VerificationContext};
use crate::verification_report::{
    emit_verbose_report_if_enabled, VerificationReport, VerificationReportOptions,
};
use crate::VerifyResult;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::{Expr, FnArg, ItemFn, Pat};

/// A proof to be verified.
///
/// Builder pattern for constructing verification contexts.
#[derive(Debug, Clone, Default)]
#[must_use]
pub struct Proof {
    /// Name of this proof (for error messages).
    /// Set by `Proof::new` and read by tests; not yet consumed by verification
    /// error paths in production builds.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) name: String,
    /// Variables in this proof
    pub(crate) variables: Vec<(String, String)>,
    /// Assumptions (preconditions)
    pub(crate) assumptions: Vec<(String, String)>,
    /// Assertions (things to prove)
    pub(crate) assertions: Vec<(String, String)>,
}

impl Proof {
    /// Creates a new proof with the given name.
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_owned(),
            ..Default::default()
        }
    }

    /// Adds a variable declaration.
    ///
    /// # Postcondition
    ///
    /// result.variables.len() == old(self.variables.len()) + 1
    pub fn with_variable(mut self, name: &str, ty: &str) -> Self {
        self.variables.push((name.to_owned(), ty.to_owned()));
        self
    }

    /// Adds an assumption (precondition).
    ///
    /// # Postcondition
    ///
    /// result.assumptions.len() == old(self.assumptions.len()) + 1
    pub fn with_assumption(mut self, name: &str, condition: &str) -> Self {
        self.assumptions
            .push((name.to_owned(), condition.to_owned()));
        self
    }

    /// Adds an assertion to prove.
    ///
    /// The condition string is used as both the assertion name and condition,
    /// providing descriptive error messages on verification failure.
    ///
    /// # Postcondition
    ///
    /// result.assertions.len() == old(self.assertions.len()) + 1
    pub fn with_assertion(mut self, condition: &str) -> Self {
        let cond = condition.to_owned();
        self.assertions.push((cond.clone(), cond));
        self
    }

    /// Adds a named assertion to prove.
    ///
    /// # Postcondition
    ///
    /// result.assertions.len() == old(self.assertions.len()) + 1
    pub fn with_named_assertion(mut self, name: &str, condition: &str) -> Self {
        self.assertions
            .push((name.to_owned(), condition.to_owned()));
        self
    }

    /// Converts to a VerificationContext.
    pub fn to_context(&self) -> VerificationContext {
        let mut ctx = VerificationContext::new();

        for (name, ty) in &self.variables {
            ctx.declare_var_typed(name, TrustVcType::parse_or_opaque(ty));
        }

        for (name, condition) in &self.assumptions {
            ctx.push_obligation(ProofObligation::assume(name, condition));
        }

        for (name, condition) in &self.assertions {
            ctx.push_obligation(ProofObligation::assert(name, condition));
        }

        ctx
    }
}

/// Main verifier entry point.
pub struct Verifier;

fn run_context_with_options(
    ctx: &VerificationContext,
    options: VerificationReportOptions,
) -> VerifyResult {
    if options.verbose() {
        let report = ctx.verify_with_report(options);
        emit_verbose_report_if_enabled(&report, options);
        return report.result().clone();
    }

    ctx.verify()
}

impl Verifier {
    /// Verifies a proof.
    pub fn verify(proof: &Proof) -> VerifyResult {
        let ctx = proof.to_context();
        run_context_with_options(&ctx, VerificationReportOptions::from_env())
    }

    /// Verifies a proof and returns the sidecar report.
    pub fn verify_with_report(
        proof: &Proof,
        options: VerificationReportOptions,
    ) -> VerificationReport {
        let ctx = proof.to_context();
        ctx.verify_with_report(options)
    }

    /// Verifies a verification context directly.
    pub fn verify_context(ctx: &VerificationContext) -> VerifyResult {
        run_context_with_options(ctx, VerificationReportOptions::from_env())
    }

    /// Verifies a verification context directly and returns the sidecar report.
    pub fn verify_context_with_report(
        ctx: &VerificationContext,
        options: VerificationReportOptions,
    ) -> VerificationReport {
        ctx.verify_with_report(options)
    }

    /// Extracts and verifies VCs from an annotated function AST.
    ///
    /// This is the key function for #751 - it bridges the gap between
    /// proc macro output and ay verification.
    ///
    /// # Process
    /// 1. Extract function parameters as variables
    /// 2. Add return value variable if function has a return type
    /// 3. Find requires/ensures from attributes
    /// 4. Find assertions in the function body
    /// 5. Build VerificationContext
    /// 6. Run ay verification
    pub fn verify_function(func: &ItemFn) -> VerifyResult {
        match Self::verify_function_inner(func) {
            Ok(result) => result,
            Err(err) => VerifyResult::from(err),
        }
    }

    fn verify_function_inner(func: &ItemFn) -> TrustVcResult<VerifyResult> {
        let mut ctx = VerificationContext::new();

        // 1. Extract function parameters as variables
        for input in &func.sig.inputs {
            if let FnArg::Typed(pat_type) = input {
                if let Pat::Ident(pat_ident) = &*pat_type.pat {
                    let var_name = pat_ident.ident.to_string();
                    let var_type = extract_type_string(&pat_type.ty);
                    ctx.declare_var_typed(&var_name, TrustVcType::parse_or_opaque(&var_type));
                }
            }
        }

        // 2. Add return value variable if function has a return type
        if let syn::ReturnType::Type(_, ty) = &func.sig.output {
            let return_type = extract_type_string(ty);
            ctx.declare_var_typed("result", TrustVcType::parse_or_opaque(&return_type));
        }

        // 3. Extract requires/ensures from attributes
        // Look for #[requires(...)] and #[ensures(...)] attributes
        for attr in &func.attrs {
            let attr_name = attr.path().segments.last().map(|segment| &segment.ident);
            if let Some(attr_name) = attr_name {
                if attr_name == "requires" {
                    let expr = attr.parse_args::<Expr>().map_err(|source| {
                        malformed_contract_attribute_error("requires", "precondition", source)
                    })?;
                    let condition = extract_condition_from_expr(&expr, &ctx);
                    ctx.push_obligation(ProofObligation::assume("requires", &condition));
                } else if attr_name == "ensures" {
                    let expr = attr.parse_args::<Expr>().map_err(|source| {
                        malformed_contract_attribute_error("ensures", "postcondition", source)
                    })?;
                    let condition = extract_condition_from_expr(&expr, &ctx);
                    ctx.push_obligation(ProofObligation::assert("ensures", &condition));
                }
            }
        }

        // 4. Find assertions in the function body
        extract_assertions_from_block(&func.block, &mut ctx)?;

        // 5. Verify the collected VCs
        Ok(run_context_with_options(
            &ctx,
            VerificationReportOptions::from_env(),
        ))
    }
}

/// Extracts a type string from a syn::Type for variable declaration
fn extract_type_string(ty: &syn::Type) -> String {
    use quote::quote;
    match ty {
        syn::Type::Path(type_path) => {
            let path = &type_path.path;
            // Ghost<T>, Tracked<T>, Proph<T>, and Snapshot<T> erase to T at SMT level.
            if let Some(seg) = path.segments.last() {
                let name = seg.ident.to_string();
                if (name == "Tracked" || name == "Ghost" || name == "Proph" || name == "Snapshot")
                    && path.segments.len() == 1
                {
                    if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                        if let Some(syn::GenericArgument::Type(inner)) = args.args.first() {
                            return extract_type_string(inner);
                        }
                    }
                }
            }
            quote!(#path).to_string().replace(' ', "")
        }
        syn::Type::Reference(type_ref) => extract_type_string(&type_ref.elem),
        _ => quote!(#ty).to_string().replace(' ', ""),
    }
}

/// Extracts a condition string from a syn::Expr.
///
/// Converts to string via `quote!()`. The typed pipeline (#1927) lowers these
/// strings to `TrustVcExpr` in `prepare_context()` before encoding.
/// Step 3b of #1866 will migrate proc macros to emit `TrustVcExpr` directly,
/// eliminating this string intermediary.
fn extract_condition_from_expr(expr: &Expr, _ctx: &VerificationContext) -> String {
    use quote::quote;
    quote!(#expr).to_string()
}

fn malformed_contract_attribute_error(
    attribute: &'static str,
    dropped_contract: &'static str,
    source: syn::Error,
) -> TrustVcError {
    TrustVcError::Encoding {
        context: "verify function",
        detail: format!(
            "Failed to parse #[{}] attribute: {} — this would silently drop the {}",
            attribute, source, dropped_contract
        ),
    }
}

/// Extracts assertions from a block of code
fn extract_assertions_from_block(
    block: &syn::Block,
    ctx: &mut VerificationContext,
) -> TrustVcResult<()> {
    use syn::visit::Visit;

    struct AssertionFinder<'a> {
        ctx: &'a mut VerificationContext,
        parse_error: Option<TrustVcError>,
    }

    impl<'ast> Visit<'ast> for AssertionFinder<'_> {
        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            if self.parse_error.is_some() {
                return;
            }
            // Look for assert! and trust_vc::assert! macros
            if mac
                .path
                .segments
                .last()
                .map(|s| s.ident == "assert")
                .unwrap_or(false)
            {
                // Parse the condition argument from assert!(cond, ...)
                match parse_assert_condition(mac) {
                    Ok(expr) => {
                        let condition = extract_condition_from_expr(&expr, self.ctx);
                        self.ctx
                            .push_obligation(ProofObligation::assert("assert", &condition));
                    }
                    Err(source) => {
                        self.parse_error = Some(TrustVcError::Encoding {
                            context: "extract assertions from block",
                            detail: format!(
                            "Failed to parse assert!() expression: {} — this would silently drop the assertion",
                                source
                            ),
                        });
                    }
                }
            }
        }
    }

    let mut finder = AssertionFinder {
        ctx,
        parse_error: None,
    };
    finder.visit_block(block);
    if let Some(err) = finder.parse_error {
        return Err(err);
    }
    Ok(())
}

fn parse_assert_condition(mac: &syn::Macro) -> Result<Expr, syn::Error> {
    let parser = Punctuated::<Expr, syn::Token![,]>::parse_terminated;
    let mut args = parser.parse2(mac.tokens.clone())?.into_iter();
    args.next()
        .ok_or_else(|| syn::Error::new_spanned(mac, "assert! requires a condition expression"))
}

/// Macro for ergonomic proof definition.
///
/// # Example
///
/// ```no_run
/// let proof = trust_vc_core::proof! {
///     name: "identity_law",
///     vars: { x: i32 },
///     assume: { positive: "x > 0" },
///     assert: { nonneg: "x >= 0" }
/// };
/// ```
#[macro_export]
macro_rules! proof {
    (
        name: $name:expr,
        $(vars: { $($var_name:ident : $var_ty:ty),* $(,)? },)?
        $(assume: { $($asm_name:ident : $asm_cond:expr),* $(,)? },)?
        $(assert: { $($ast_name:ident : $ast_cond:expr),* $(,)? })?
    ) => {{
        let mut proof = $crate::verify::Proof::new($name);
        $(
            $(
                proof = proof.with_variable(stringify!($var_name), stringify!($var_ty));
            )*
        )?
        $(
            $(
                proof = proof.with_assumption(stringify!($asm_name), $asm_cond);
            )*
        )?
        $(
            $(
                proof = proof.with_named_assertion(stringify!($ast_name), $ast_cond);
            )*
        )?
        proof
    }};
}

#[cfg(test)]
mod tests;
