pub use self::Q as Sub;
verus!{
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct W<X> { pub w: S<X> }
impl<X: Sub> W<X> {
    pub proof fn f(&self) ensures self.w.mm() == 2 { }
}
} // verus!
