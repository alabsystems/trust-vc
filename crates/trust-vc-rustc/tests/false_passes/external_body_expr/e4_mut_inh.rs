::verus_builtin_macros::verus!{
pub struct T<A>(pub A);
pub struct R { pub a: u8 }
#[verifier::external]
fn g_ptr() -> fn() { h_unit }
#[verifier::external]
fn h_unit() {}
#[verifier::external]
fn g_mut(x: &mut u8) -> &mut u8 { x }
#[verifier::external]
fn g_box<A>(a: A) -> Box<A> { Box::new(a) }
#[verifier::external]
fn g_dyn() -> &'static dyn core::fmt::Debug { &1u8 }
#[verifier::external]
fn g_u8() -> u8 { 1 }
pub struct S {}
impl S { #[verifier::external_body] fn f(&self) { g_mut(&mut 1u8); } }
fn user(s: &S) {{ s.f(); }}
}
