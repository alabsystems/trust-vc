pub trait Sub: Tr { }
pub trait Sub2: Sub { }
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
pub struct W0<X> { pub w: S<X> }
impl<X: Sub2> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
} // verus!
