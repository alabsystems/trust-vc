
verus!{
pub struct S<X> { pub x: X }
#[verifier::external]
pub trait Sub2: Sub { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct Z { pub z: u8 }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
#[verifier::external]
pub trait Sub: Q + Tr { }
pub trait Q { }
pub trait Tr { }
pub fn f0<X: Sub2>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub struct W1<X> { pub w: S<X> }
impl<X: Sub2> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
pub trait V2 {
    proof fn f2<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
