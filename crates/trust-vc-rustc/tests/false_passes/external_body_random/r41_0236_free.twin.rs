::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
pub struct T2<A, B>(pub A, pub B);
pub struct S2(pub u8);
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
fn g_u8() -> u8 { 1 }
#[verifier::external]
fn g_c() -> C<'a'> { C(0) }
#[verifier::external]
fn g_wu() -> WU<u8> { WU(1) }
#[verifier::external]
fn g_id<A>(a: A) -> A { a }
#[verifier::external_body]
fn f() { Some((T(g_id(g_u8())).0)); }
fn user() { f(); }
}
