// Test demonstrating the stringify! problem destroying type information
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! This test demonstrates how stringify! destroys type information,
//! making real verification impossible.

#[test]
fn test_stringify_loses_types() {
    // This test shows the fundamental problem with using stringify!

    #[allow(unused_variables)] // Variables are only used in stringify!
    let x: i32 = 5;
    #[allow(unused_variables)] // Variables are only used in stringify!
    let y: u64 = 10;

    // When we stringify this expression:
    let expr = stringify!(x + y);

    // We get just the string "x + y" with no type info
    assert_eq!(expr, "x + y");

    // The verifier has no idea that:
    // - x is an i32
    // - y is a u64
    // - This addition requires type conversion
    // - The result type depends on Rust's type coercion rules

    // This is why ay returns Unknown for most queries
}

#[test]
fn test_stringify_loses_scope() {
    // Stringify also loses scope information

    fn inner() {
        #[allow(unused_variables)] // Used in stringify!
        let x = 1;
        let _expr = stringify!(x > 0);
        // Just becomes "x > 0" - no context about which x
    }

    #[allow(unused_variables)] // Used in stringify!
    let x = 2;
    let _expr = stringify!(x > 0);
    // Also becomes "x > 0" - indistinguishable from inner's x

    inner();
}

#[test]
fn test_stringify_loses_semantics() {
    // Semantic information is completely lost

    #[allow(dead_code)] // Intentionally unused to demonstrate the problem
    struct Point {
        x: i32,
        y: i32,
    }

    impl Point {
        #[allow(dead_code)] // Intentionally unused to demonstrate the problem
        fn distance_squared(&self) -> i32 {
            self.x * self.x + self.y * self.y
        }
    }

    #[allow(unused_variables)] // Used in stringify!
    let p = Point { x: 3, y: 4 };

    // This complex method call:
    let _expr = stringify!(p.distance_squared() == 25);

    // Becomes just "p.distance_squared() == 25"
    // The verifier has no idea:
    // - What Point is
    // - What distance_squared does
    // - How to evaluate this
}

#[test]
fn test_what_we_need_instead() {
    // What we SHOULD do: parse the AST properly

    // Instead of stringify!(x + y > 0), we need:
    // 1. Parse the TokenStream into syn::Expr
    // 2. Walk the AST to find variables and their types
    // 3. Generate SMT terms with proper type annotations
    // 4. Maintain a symbol table with scope information

    // Example of what the verifier should see:
    // - Variable(x, Type::I32, Value::5)
    // - Variable(y, Type::U64, Value::10)
    // - BinOp(Add, Var(x), Var(y)) with type coercion
    // - BinOp(Gt, AddResult, Literal(0, Type::I32))

    // This is the only way to do real verification
}
