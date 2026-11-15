
verus!{
pub trait Tr { }
#[verifier::external]
pub trait Sub2: Sub { }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8;
}
#[verifier::external]
pub trait Sub: Q { }
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait V0 {
    proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
