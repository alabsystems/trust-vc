::verus_builtin_macros::verus!{
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
fn g_wu() -> WU<u8> { WU(1) }
fn f<A>(a: A) where WU<u8>: Sized {}
fn user() { f(1u8); }
}
