pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct Z { pub z: u8 }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait Tr { }
pub trait Q { }
pub proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
pub fn f1<X: Sub2>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
