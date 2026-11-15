pub trait Sub: Tr { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8;
}
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub fn f0<X: Sub>(s: S<X>) -> (r: u8) ensures r == s.mm() { 2 }
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub struct W2<X> { pub w: S<X> }
impl<X: Sub> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() == 2 { }
}
} // verus!
