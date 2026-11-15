
verus!{
pub trait Tr { }
pub struct Z { pub z: u8 }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Q { }
#[verifier::external]
pub trait Sub: Tr { }
#[verifier::external]
pub trait Sub2: Sub { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct S<X> { pub x: X }
pub proof fn f0<X: Sub2>(s: S<X>) { assert(s.mm() == 2); }
pub trait V1 {
    proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
pub proof fn f2<X>(s: S<X>) where X: Sub2 ensures s.mm() == 2 { }
} // verus!
