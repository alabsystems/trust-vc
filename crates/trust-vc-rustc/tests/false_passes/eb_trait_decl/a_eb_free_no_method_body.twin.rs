::verus_builtin_macros::verus!{
#[verifier::loop_isolation(false)]
fn f() { no_method_body() }
fn user() { f(); }
}
