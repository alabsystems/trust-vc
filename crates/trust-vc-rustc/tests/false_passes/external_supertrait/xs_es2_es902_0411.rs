pub trait Sub<A>: Q<A> { }
verus!{
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q<A> { }
pub struct S<X> { pub x: X }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub proof fn f0<X: Sub<u8>>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
