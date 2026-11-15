
verus!{
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
#[verifier::external]
pub trait Sub<A>: Q<A> { }
pub trait Q<A> { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X>(s: S<X>) where X: Sub<u8> ensures s.mm() == 2 { }
} // verus!
