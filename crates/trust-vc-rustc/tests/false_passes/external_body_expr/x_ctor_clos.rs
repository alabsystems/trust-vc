::verus_builtin_macros::verus!{
pub struct T<F>(pub F);
#[verifier::external_body]
fn f() { T(|x: u8| { recommends([true]); x }); }
fn user() { f(); }
}
