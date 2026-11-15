
verus!{
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
#[verifier::external]
pub trait Sub: Q { }
pub struct Z { pub z: u8 }
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
pub proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
pub open spec fn g2<X: Sub>(s: S<X>) -> u8 { s.mm() }
pub proof fn f2<X: Sub>(s: S<X>) ensures g2(s) == 2 { }
} // verus!
