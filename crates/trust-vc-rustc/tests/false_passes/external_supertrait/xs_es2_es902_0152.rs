pub trait Sub: Tr { }
verus!{
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait Tr { }
pub trait Q { }
pub trait Tr2 { }
impl<X: Tr> Tr2 for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub trait V1 {
    proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
}
} // verus!
