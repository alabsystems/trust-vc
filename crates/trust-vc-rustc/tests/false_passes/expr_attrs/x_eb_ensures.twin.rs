::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() -> (r: u64) ensures r == 5 { 5 }
}
