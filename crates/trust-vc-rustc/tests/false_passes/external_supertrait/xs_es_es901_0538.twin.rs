
verus!{
pub trait U {
    spec fn mm(&self) -> u8;
}
#[verifier::external]
pub use self::Q as Sub;
pub trait Tr { }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q<A> { }
pub struct S<X> { pub x: X }
pub fn f0<X: Sub<u8>>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
