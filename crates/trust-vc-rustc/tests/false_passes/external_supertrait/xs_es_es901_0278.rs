pub trait Sub: Q { }
verus!{
pub trait Q { }
pub struct S<X> { pub x: X }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Tr { }
pub proof fn f0<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub struct W1<X> { pub w: S<X> }
impl<X: Sub> W1<X> {
    pub proof fn f1(&self) ensures self.w.mm() == 2 { }
}
} // verus!
