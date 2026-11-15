pub trait Sub: Q { }
pub use self::Q as Sub2;
verus!{
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait Tr { }
pub struct Z { pub z: u8 }
pub fn f0<X: Sub2>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
