pub trait Sub<A>: Q<A> { }
verus!{
pub trait Q<A> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X: Q<u8>> Tr for S<X> { }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub proof fn f0<X>(s: S<X>) where X: Sub<u8> ensures s.mm() == 2 { }
} // verus!
