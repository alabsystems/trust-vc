::verus_builtin_macros::verus!{
fn g(x: u64) -> (r: u64) { (#[verifier::no_such_attribute] x).clone() }
}
