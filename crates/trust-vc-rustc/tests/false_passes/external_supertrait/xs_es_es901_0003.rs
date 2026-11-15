
verus!{
pub trait Q { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
#[verifier::external]
pub trait Sub: Q + Tr { }
pub struct S<X> { pub x: X }
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() != 2 { }
pub fn f1<X: Sub>(s: S<X>) -> (r: u8) ensures r != s.mm() { 2 }
} // verus!
