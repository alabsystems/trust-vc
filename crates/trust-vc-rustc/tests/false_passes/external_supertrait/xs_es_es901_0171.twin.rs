
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub trait Q { }
pub struct Z { pub z: u8 }
#[verifier::external]
pub use self::Tr as Sub;
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Tr2 { }
impl<X: Tr> Tr2 for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub open spec fn g0<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f0<X: Sub>(s: S<X>) ensures g0(s) == 2 { }
} // verus!
