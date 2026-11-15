pub trait Sub: Q { }
verus!{
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct Z { pub z: u8 }
pub trait Q { }
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct W0<X> { pub w: S<X> }
impl<X: Sub> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub proof fn f1<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub proof fn f2<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
} // verus!
