
verus!{
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
#[verifier::external]
pub use self::Q as Sub;
pub trait Tr { }
pub trait Q { }
pub struct S<X> { pub x: X }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct Z { pub z: u8 }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub struct W1<X> { pub w: S<X> }
impl<X: Sub> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
pub struct W2<X> { pub w: S<X> }
impl<X: Sub> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() == 2 { }
}
} // verus!
