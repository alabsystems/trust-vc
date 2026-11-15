::verus_builtin_macros::verus!{
#[verifier::external_body]
fn f(x: u64) decreases x { }
}
