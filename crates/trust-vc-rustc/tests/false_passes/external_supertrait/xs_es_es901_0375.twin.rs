pub use self::Tr as Sub;
verus!{
impl<X: Tr> Tr2 for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub struct S<X> { pub x: X }
pub trait Tr2 { }
pub struct Z { pub z: u8 }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub trait Q { }
pub trait Tr { }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
} // verus!
