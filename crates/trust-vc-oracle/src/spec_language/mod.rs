//! trust-vc-oracle — Mini specification language parser and AST
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Provides a structured AST for formal specifications so that the oracle can
//! generate and manipulate specs programmatically rather than through raw string
//! concatenation. Includes parsing from text, pretty-printing back to text, and
//! semantic transformations (substitution, weakening, strengthening).

mod ast;
mod parser;
mod printer;
#[cfg(test)]
mod tests;
mod transformer;

pub use ast::*;
pub use parser::*;
pub use printer::*;
pub use transformer::*;
