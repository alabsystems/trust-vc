
verus!{
#[verifier::external]
pub trait Sub: Tr { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub trait Tr { }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub trait V1 {
    proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
pub proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
