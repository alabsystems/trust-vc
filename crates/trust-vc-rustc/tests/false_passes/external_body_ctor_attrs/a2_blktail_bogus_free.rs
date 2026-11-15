::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
#[verifier::external]
fn g_u8() -> u8 { 1 }
pub struct S(pub u8);
#[verifier::external_body]
fn f() { T({ T(#[verifier::bogus] 1u8) }); }
fn user() { f(); }
}
