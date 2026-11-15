::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
#[verifier::external_body]
fn e() {}
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) -> (r: u8) ensures r == 1 { consume(s); 1 }
}
