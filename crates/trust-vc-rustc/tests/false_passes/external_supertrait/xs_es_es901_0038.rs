
verus!{
#[verifier::external]
pub trait Sub: Q { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait V0 {
    proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
pub struct W1<X> { pub w: S<X> }
impl<X: Sub> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
pub proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
