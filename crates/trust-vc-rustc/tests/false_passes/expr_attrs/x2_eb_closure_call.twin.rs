::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { (|| { 1u64 })(); }
}
