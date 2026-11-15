
verus!{
#[verifier::external]
pub trait Sub: Tr { }
#[verifier::external]
pub use self::Tr as Sub2;
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub trait Tr { }
pub struct S<X> { pub x: X }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f0<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
pub fn f2<X: Sub2>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
} // verus!
