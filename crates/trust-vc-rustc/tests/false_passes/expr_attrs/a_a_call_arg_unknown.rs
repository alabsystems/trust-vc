::verus_builtin_macros::verus!{
fn e(x: u64) -> (r: u64) ensures r == x { x }
fn g() { let y = e(#[verifier::no_such_attribute] 3); assert(y == 3); }
}
