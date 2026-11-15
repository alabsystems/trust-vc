pub use self::Q as Sub;
verus!{
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q<u8>> Tr for S<X> { }
pub trait Tr { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub trait Q<A> { }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub<u8>> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub proof fn f1<X>(s: S<X>) where X: Sub<u8> ensures s.mm() == 2 { }
pub struct W2<X> { pub w: S<X> }
impl<X: Sub<u8>> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() == 2 { }
}
} // verus!
