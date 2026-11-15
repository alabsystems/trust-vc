::verus_builtin_macros::verus!{
#[verifier::opaque]
pub open spec fn o() -> int { 1 }
#[verifier::external_body]
fn e() { proof { reveal(o); } }
fn f() {}
}
