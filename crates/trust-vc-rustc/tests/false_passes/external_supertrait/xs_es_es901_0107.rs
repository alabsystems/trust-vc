
verus!{
#[verifier::external]
pub trait Sub: Q + Tr { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
pub trait V0 {
    proof fn f0<X: Sub>(s: S<X>) ensures s.mm() != 3 { }
}
} // verus!
