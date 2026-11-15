
verus!{
pub struct Z { pub z: u8 }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
#[verifier::external]
pub trait Sub: Q { }
pub struct S<X> { pub x: X }
pub proof fn f0<X: Sub>(s: S<X>) ensures s.mm() != 3 { }
} // verus!
