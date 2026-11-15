::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
#[verifier::external_body]
fn f() { T({ }); }
fn user() { f(); }
}
