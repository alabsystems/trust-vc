
verus!{
pub trait Q<A> { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
#[verifier::external]
pub use self::Q as Sub;
pub proof fn f0<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
pub fn f1<X: Sub<u8>>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
