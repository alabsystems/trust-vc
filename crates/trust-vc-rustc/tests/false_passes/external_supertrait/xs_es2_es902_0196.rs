pub trait Sub<A>: Q<A> { }
verus!{
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
impl<X: Q<u8>> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q<A> { }
pub proof fn f0<X: Sub<u8>>(s: S<X>) { assert(s.mm() != 2); }
pub proof fn f1<X: Sub<u8>>(s: S<X>) { assert(s.mm() != 2); }
pub proof fn f2<X: Sub<u8>>(s: S<X>) ensures s.mm() != 2 { }
} // verus!
