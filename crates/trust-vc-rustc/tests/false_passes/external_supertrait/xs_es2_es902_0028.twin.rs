
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct S<X> { pub x: X }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
#[verifier::external]
pub use self::Q as Sub;
impl<X: Q<u8>> Tr for S<X> { }
pub trait Tr { }
pub trait Q<A> { }
pub struct Z { pub z: u8 }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub<u8>> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() != 3 { }
}
} // verus!
