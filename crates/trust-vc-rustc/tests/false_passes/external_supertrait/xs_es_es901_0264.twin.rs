pub use self::Tr as Sub;
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub trait Tr2 { }
pub trait Q { }
impl<X: Tr> Tr2 for S<X> { }
pub trait Tr { }
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub struct W1<X> { pub w: S<X> }
impl<X: Sub> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
} // verus!
