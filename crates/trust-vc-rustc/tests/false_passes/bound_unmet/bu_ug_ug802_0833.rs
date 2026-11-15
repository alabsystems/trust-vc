verus!{
pub struct S<X> { pub x: X }
impl V for Z {
    proof fn lv(&self) { }
}
pub trait V {
    proof fn lv(&self) where Self: U + Q ensures self.mm() == 2;
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait Q { }
impl<X: Q> Tr for S<X> { }
impl Tr for u8 { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
    proof fn lm1(&self) { }
}
pub trait U {
    proof fn lm1(&self) where Self: Q ensures self.mm() == 2;
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
} // verus!
