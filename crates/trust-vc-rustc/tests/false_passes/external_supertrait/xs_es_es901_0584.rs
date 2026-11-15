pub trait Sub: Tr { }
verus!{
pub trait Tr2 { }
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
impl<X: Tr> Tr2 for S<X> { }
pub proof fn f0<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
} // verus!
