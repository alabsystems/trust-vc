pub trait Sub: Q { }
verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub proof fn f<X: Sub>(s: S<X>) ensures s.mm() == 2 { }
} // verus!
