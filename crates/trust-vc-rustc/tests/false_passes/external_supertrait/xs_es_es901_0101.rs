pub trait Sub: Tr { }
verus!{
pub trait U {
    spec fn mm(&self) -> u8 where Self: Tr2;
}
pub trait Tr { }
pub trait Tr2 { }
impl<X: Tr> Tr2 for S<X> { }
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr2 { 2 }
}
pub trait Q { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub proof fn f0<X>(s: S<X>) where X: Sub ensures s.mm() == 2 { }
pub proof fn f1<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
pub proof fn f2<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
