pub use self::Q as Sub;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
