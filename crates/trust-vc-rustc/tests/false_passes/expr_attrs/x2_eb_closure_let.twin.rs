::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f() { let c = || { 1u64 }; }
}
