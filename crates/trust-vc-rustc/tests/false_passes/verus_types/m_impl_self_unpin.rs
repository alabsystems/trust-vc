::verus_builtin_macros::verus!{
#[verifier::external]
pub struct WU<D: Unpin>(pub D);
#[verifier::external]
fn g_wu() -> WU<u8> { WU(1) }
pub trait Tr { }
impl Tr for WU<u8> { }
fn user() { }
}
