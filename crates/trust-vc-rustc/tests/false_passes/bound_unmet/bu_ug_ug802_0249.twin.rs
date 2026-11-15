verus!{
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub struct S<X> { pub x: X } impl Tr for Z { }
impl Q for u8 { }
pub trait Q { }
pub struct Z { pub z: u8 }
impl Q for Z { }
impl V for Z {
    proof fn lv(&self) { }
}
pub trait Tr { }
impl<X: Q> Tr for S<X> { }
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
