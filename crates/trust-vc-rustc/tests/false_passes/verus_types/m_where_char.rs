::verus_builtin_macros::verus!{
#[verifier::external]
pub struct C<const X: char>(pub u8);
#[verifier::external]
fn g_c() -> C<'a'> { C(0) }
fn f<A>(a: A) where C<'a'>: Sized {}
fn user() { f(1u8); }
}
