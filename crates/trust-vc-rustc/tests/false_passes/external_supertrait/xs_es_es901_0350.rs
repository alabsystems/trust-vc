pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub trait Tr { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct Z { pub z: u8 }
impl<X: Q> Tr for S<X> { }
pub struct S<X> { pub x: X }
pub trait Q { }
pub struct W0<X> { pub w: S<X> }
impl<X: Sub2> W0<X> {
    pub proof fn f0(&self) ensures self.w.mm() == 2 { }
}
pub trait V1 {
    proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
pub struct W2<X> { pub w: S<X> }
impl<X: Sub2> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() == 2 { }
}
} // verus!
