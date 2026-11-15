
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub trait Q { }
impl<X: Q> Tr for S<X> { }
#[verifier::external]
pub trait Sub: Q + Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait Tr { }
#[verifier::external]
pub trait Sub2: Sub { }
pub proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
