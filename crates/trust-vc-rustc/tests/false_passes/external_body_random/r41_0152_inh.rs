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
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { if true { (1u8 as u8) } else { (T(#[verifier::proof_note("a")] 1u8).0) }; S2(#[verifier::proof_note("a")] #[verifier::proof_note("b")] (T(#[verifier::bogus] (g_u8() as u8)).0)); 1u8; } }
fn user(s: &S) { s.f(); }
}
