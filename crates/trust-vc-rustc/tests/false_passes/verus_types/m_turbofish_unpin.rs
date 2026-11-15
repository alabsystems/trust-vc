::verus_builtin_macros::verus!{
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
fn g_wu() -> WU<u8> { WU(1) }
fn id<A>(a: u8) -> u8 { a }
fn user() { let x = id::<WU<u8>>(1); }
}
