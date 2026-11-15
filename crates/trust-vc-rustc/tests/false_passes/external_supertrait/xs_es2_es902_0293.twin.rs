pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub2> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() != 3 { }
}
} // verus!
