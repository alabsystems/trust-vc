pub use self::Tr as Sub;
verus!{
pub struct Z { pub z: u8 }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub trait Tr { }
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f1<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
pub struct W2<X> { pub w: S<X> }
impl<X: Sub> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() == 2 { }
}
} // verus!
