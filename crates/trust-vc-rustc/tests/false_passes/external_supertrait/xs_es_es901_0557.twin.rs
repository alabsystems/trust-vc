
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
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub proof fn f0<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub open spec fn g1<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f1<X: Sub>(s: S<X>) ensures g1(s) == 2 { }
pub open spec fn g2<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f2<X: Sub>(s: S<X>) ensures g2(s) == 2 { }
} // verus!
