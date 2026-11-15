pub use self::Q as Sub;
verus!{
pub trait Q<A> { }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
impl<X: Q<u8>> Tr for S<X> { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub open spec fn g0<X: Sub<u8>>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub<u8>>(s: S<X>) ensures g0(s) != 3 { }
} // verus!
