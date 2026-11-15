::verus_builtin_macros::verus!{
#[verifier::external_body]
fn e() {}
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) { consume(s); }
}
