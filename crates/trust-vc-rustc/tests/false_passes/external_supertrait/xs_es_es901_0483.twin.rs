pub use self::Q as Sub;
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
pub struct S<X> { pub x: X }
pub trait Q { }
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() != 3); }
pub trait V1 {
    proof fn f1<X: Sub>(s: S<X>) ensures s.mm() != 3 { }
}
pub struct W2<X> { pub w: S<X> }
impl<X: Sub> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() != 3 { }
}
} // verus!
