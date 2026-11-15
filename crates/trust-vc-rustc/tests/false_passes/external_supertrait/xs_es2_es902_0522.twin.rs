pub use self::Q as Sub;
verus!{
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() != 2 { }
}
pub struct W1<X> { pub w: S<X> }
impl<X: Sub> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() != 2 { }
}
} // verus!
