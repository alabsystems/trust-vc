pub trait Sub: Q { }
verus!{
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
impl<X: Q> U for S<X> {
    open spec fn mm(&self) -> u8 { 2 }
}
pub trait U {
    spec fn mm(&self) -> u8;
}
pub trait Q { }
pub trait Tr { }
pub proof fn f0<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
pub proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
pub proof fn f2<X: Sub>(s: S<X>) { assert(s.mm() == 2); }
} // verus!
