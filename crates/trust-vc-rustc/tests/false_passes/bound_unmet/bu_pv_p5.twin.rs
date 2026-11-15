verus!{
pub struct S<X> { pub x: X }
pub trait Tr { }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q> V for S<X> {
    proof fn lv(&self) { }
}
} // verus!
