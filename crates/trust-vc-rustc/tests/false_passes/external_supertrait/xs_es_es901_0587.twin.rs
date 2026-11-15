
verus!{
pub trait Q<A> { }
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct Z { pub z: u8 }
#[verifier::external]
pub use self::Q as Sub;
impl<X: Q<u8>> Tr for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub open spec fn g0<X: Sub<u8>>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub<u8>>(s: S<X>) ensures g0(s) == 2 { }
} // verus!
