pub trait Sub: Q { }
verus!{
pub struct S<X> { pub x: X }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 5 }
}
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() != 2 { }
}
} // verus!
