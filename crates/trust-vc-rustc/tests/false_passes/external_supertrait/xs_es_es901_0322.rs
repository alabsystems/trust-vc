pub trait Sub<A>: Q<A> { }
verus!{
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q<A> { }
pub struct Z { pub z: u8 }
pub open spec fn g0<X: Sub<u8>>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub<u8>>(s: S<X>) ensures g0(s) == 2 { }
pub proof fn f1<X>(s: S<X>) where X: Sub<u8> ensures s.mm() == 2 { }
} // verus!
