pub trait Sub<A>: Q<A> { }
verus!{
pub trait Tr { }
pub trait Q<A> { }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X: Q<u8>> Tr for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct S<X> { pub x: X }
pub proof fn f0<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
