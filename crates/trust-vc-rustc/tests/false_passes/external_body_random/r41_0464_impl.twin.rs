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
pub trait Tr { fn f(&self); }
pub struct S {}
impl Tr for S { #[verifier::external_body] fn f(&self) { { T({ g_u8(); 1u8 }); } S2(if true { if true { 1u8 } else { g_u8() } } else { (g_u8()).clone() }); } }
fn user(s: &S) { s.f(); }
}
