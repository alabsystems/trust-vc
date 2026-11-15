::verus_builtin_macros::verus!{
#[verifier::proof]
#[verifier::exec]
fn f() { }
fn user() { f(); }
}
