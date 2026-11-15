pub trait Sub: Tr { }
pub trait Sub2: Sub { }
verus!{
impl<X: Tr> Tr2 for S<X> { }
pub struct S<X> { pub x: X }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub struct Z { pub z: u8 }
pub trait Tr2 { }
pub trait Tr { }
pub trait Q { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 5 }
}
pub trait V0 {
    proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
}
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
pub struct W2<X> { pub w: S<X> }
impl<X: Sub2> W2<X> {
    pub proof fn f2(&self) ensures self.w.mm() != 3 { }
}
} // verus!
