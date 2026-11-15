verus!{
impl<X: Q> Tr for S<X> { }
pub trait Tr { } impl Tr for Z { } impl Q for Z { }
pub trait Q { }
pub trait V {
    proof fn lv(&self) where Self: U + Q ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm1(&self) { }
    fn z0(&self) -> (r: u8) { 2 }
}
pub struct S<X> { pub x: X }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
}
impl V for Z {
    proof fn lv(&self) { }
}
pub struct Z { pub z: u8 }
} // verus!
