
verus!{
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q<A> { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl<X: Q<u8>> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
#[verifier::external]
pub use self::Q as Sub;
pub struct W0<X> { pub w: S<X> }
impl<X: Sub<u8>> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
} // verus!
