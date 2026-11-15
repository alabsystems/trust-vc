pub trait Sub: Q { }
verus!{
pub trait Tr { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
} // verus!
