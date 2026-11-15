::verus_builtin_macros::verus!{
#[verifier::external_body]
proof fn l() {}
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) -> (r: u8) ensures r == 1 { consume(s); 1 }
}
