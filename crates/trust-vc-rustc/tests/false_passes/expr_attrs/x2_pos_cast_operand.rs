::verus_builtin_macros::verus!{
fn g(x: u64) -> (r: u8) { (#[verifier::no_such_attribute] x) as u8 }
}
