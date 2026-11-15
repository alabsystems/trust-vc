pub trait Sub<A>: Q<A> { }
verus!{
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait Q<A> { }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub fn f0<X: Sub<u8>>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub fn f1<X: Sub<u8>>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
