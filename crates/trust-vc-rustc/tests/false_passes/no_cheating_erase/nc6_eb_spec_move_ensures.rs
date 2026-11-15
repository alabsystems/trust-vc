::verus_builtin_macros::verus!{
#[verifier::external_body]
spec fn u() -> bool { true }
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) -> (r: u8) ensures r == 1 { consume(s); consume(s); 1 }
}
