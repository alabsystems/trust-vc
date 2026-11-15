::verus_builtin_macros::verus!{
pub struct T<F>(pub F);
#[verifier::external_body]
fn f() { T(1u8); }
fn user() { f(); }
}
