
verus!{
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 5 }
}
pub trait Q { }
#[verifier::external]
pub trait Sub: Tr { }
pub proof fn f0<X>(s: S<X>) where X: Sub ensures s.mm() != 3 { }
} // verus!
