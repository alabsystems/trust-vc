pub use self::Tr as Sub;
verus!{
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait V0 {
    proof fn f0<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
pub struct W1<X> { pub w: S<X> }
impl<X: Sub> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
} // verus!
