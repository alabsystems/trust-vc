verus!{
pub trait Tr { } impl Tr for Z { } impl Q for Z { }
impl<X: Q> Tr for S<X> { }
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
impl V for Z {
    proof fn lv(&self) { }
}
pub trait Q { }
pub struct S<X> { pub x: X }
} // verus!
