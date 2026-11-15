
verus!{
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Q { }
pub trait Tr { }
#[verifier::external]
pub trait Sub: Q + Tr { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
} // verus!
