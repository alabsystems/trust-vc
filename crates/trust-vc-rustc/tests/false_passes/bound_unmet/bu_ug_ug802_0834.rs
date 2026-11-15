verus!{
impl<X: Q> Tr for S<X> { }
impl<X: Q> V for S<X> {
    proof fn lv(&self) { }
}
pub trait Q { }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Q for u8 { }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
pub struct S<X> { pub x: X }
impl Q for Z { }
impl<X> U for S<X> {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
} // verus!
