
verus!{
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait Tr { }
#[verifier::external]
pub use self::Q as Sub;
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub proof fn f2<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
