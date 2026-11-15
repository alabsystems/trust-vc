::verus_builtin_macros::verus!{
spec fn s(x: int) -> int { x }
fn f(x: u64) -> (r: u64) ensures r == s(#[verifier::no_such_attribute] x as int) { x }
}
