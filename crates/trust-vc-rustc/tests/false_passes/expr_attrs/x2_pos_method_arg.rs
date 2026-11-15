::verus_builtin_macros::verus!{
fn g(x: u64) -> (r: bool) { x.eq(&(#[verifier::no_such_attribute] x)) }
}
