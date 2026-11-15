
verus!{
#[verifier::external]
pub use self::Q as Sub;
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Q<A> { }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub trait Tr { }
pub struct S<X> { pub x: X }
impl<X: Q<u8>> Tr for S<X> { }
pub open spec fn g0<X: Sub<u8>>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub<u8>>(s: S<X>) ensures g0(s) == 2 { }
} // verus!
