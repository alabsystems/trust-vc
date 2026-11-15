pub trait Sub<A>: Q<A> { }
verus!{
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q<A> { }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
pub proof fn f0<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
pub trait V1 {
    proof fn f1<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
}
pub open spec fn g2<X: Sub<u8>>(s: S<X>) -> u8 { s.mm() }
pub proof fn f2<X: Sub<u8>>(s: S<X>) ensures g2(s) == 2 { }
} // verus!
