pub trait Sub: Tr { }
pub use self::Tr as Sub2;
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub fn f0<X: Sub2>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
