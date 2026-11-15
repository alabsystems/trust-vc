::verus_builtin_macros::verus!{
fn g(a: [u64; 3]) -> (r: u64) { a[#[verifier::no_such_attribute] 0] }
}
