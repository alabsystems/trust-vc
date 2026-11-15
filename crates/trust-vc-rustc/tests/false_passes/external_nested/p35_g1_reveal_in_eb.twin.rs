::verus_builtin_macros::verus!{
#[verifier::opaque]
pub open spec fn o() -> int { 1 }
// no attribute
fn e() { proof { reveal(o); } }
fn f() {}
}
