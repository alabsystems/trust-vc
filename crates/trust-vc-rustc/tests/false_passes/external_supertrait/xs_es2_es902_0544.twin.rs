pub use self::Q as Sub;
verus!{
pub trait Q { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait Tr { }
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r != s.mm() { 3 }
pub struct W1<X> { pub w: S<X> }
impl<X: Sub> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() != 3 { }
}
pub struct W2<X> { pub w: S<X> }
impl<X: Sub> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() != 3 { }
}
} // verus!
