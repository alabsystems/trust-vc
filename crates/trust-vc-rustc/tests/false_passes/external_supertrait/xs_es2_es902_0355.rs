pub trait Sub<A>: Q<A> { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q<A> { }
impl<X: Q<u8>> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct W0<X> { pub w: S<X> }
impl<X: Sub<u8>> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub trait V1 {
    proof fn f1<X: Sub<u8>>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
