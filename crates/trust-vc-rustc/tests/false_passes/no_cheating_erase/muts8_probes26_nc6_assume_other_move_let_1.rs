::verus_builtin_macros::verus!{
#[verifier::external_body]
fn nc_x_() {}
proof fn g() { assume(true); }
struct S { x: u8 }
fn consume(s: S) {}
fn f() { let s = S { x: 1 }; let a = s; let b = s; }
}
