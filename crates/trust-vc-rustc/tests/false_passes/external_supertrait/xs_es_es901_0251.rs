
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub trait Q<A> { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
#[verifier::external]
pub trait Sub<A>: Q<A> { }
impl<X: Q<u8>> Tr for S<X> { }
pub proof fn f0<X: Sub<u8>>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
