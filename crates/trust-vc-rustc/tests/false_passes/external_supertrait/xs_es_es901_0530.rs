pub trait Sub: Q + Tr { }
pub trait Sub2: Sub { }
verus!{
impl<X: Q> Tr for S<X> { }
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr;
}
pub struct Z { pub z: u8 }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct S<X> { pub x: X }
pub trait Q { }
pub trait Tr { }
pub trait V0 {
    proof fn f0<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
}
pub proof fn f1<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
pub trait V2 {
    proof fn f2<X: Sub2>(s: S<X>) ensures s.mm() != 3 { }
}
} // verus!
