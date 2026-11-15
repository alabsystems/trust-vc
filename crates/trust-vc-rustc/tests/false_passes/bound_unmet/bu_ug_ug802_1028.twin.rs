verus!{
pub trait V {
    proof fn lv(&self) where Self: U + Q ensures self.mm() == 2;
}
impl<X: Q> Tr for S<X> { }
pub struct Z { pub z: u8 } impl Q for Z { }
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub trait U {
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub trait Tr { }
pub struct S<X> { pub x: X }
impl Tr for Z { }
pub trait Q { }
impl V for Z {
    proof fn lv(&self) { }
}
} // verus!
