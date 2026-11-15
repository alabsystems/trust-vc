pub use self::Q as Sub;
verus!{
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait Tr { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() != 3 { }
}
pub fn f1<X: Sub>(s: S<X>) -> (r: u8) ensures r != s.mm() { 3 }
} // verus!
