pub trait Sub: Q { }
pub trait Sub2: Sub { }
verus!{
impl<X: Q> Tr for S<X> { }
pub trait Q { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct Z { pub z: u8 }
pub trait Tr { }
pub struct S<X> { pub x: X }
pub trait V0 {
    proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
}
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
pub proof fn f2<X: Sub2>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
