::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f(x: u64) -> (r: u64) ensures r == x { x }
}
