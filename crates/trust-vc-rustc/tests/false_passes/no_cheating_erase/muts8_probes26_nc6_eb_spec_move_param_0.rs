::verus_builtin_macros::verus!{
uninterp spec fn nc_u_() -> bool;
#[verifier::external_body]
spec fn u() -> bool { true }
struct S { x: u8 }
fn consume(s: S) {}
fn f(s: S) { consume(s); consume(s); }
}
