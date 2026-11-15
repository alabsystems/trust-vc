
verus!{
#[verifier::external]
pub use self::Tr as Sub;
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait Tr2 { }
impl<X: Tr> Tr2 for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 5 }
}
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r != s.mm() { 2 }
pub proof fn f1<X: Sub>(s: S<X>) ensures s.mm() != 2 { }
} // verus!
