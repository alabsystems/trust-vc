pub trait Sub: Tr { }
verus!{
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait Tr { }
impl<X: Tr> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
} // verus!
