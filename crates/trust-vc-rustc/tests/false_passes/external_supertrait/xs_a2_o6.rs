verus!{
pub struct S<X> { pub x: X }
pub trait Q { }
#[verifier::external]
pub trait Sub: Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub proof fn f<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
