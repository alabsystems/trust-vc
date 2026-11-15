verus!{
impl<X: Q> U for S<X> {
    fn z1(&self) -> (r: u8) where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q { }
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
}
pub struct Z { pub z: u8 }
pub struct S<X> { pub x: X }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    proof fn lm0(&self) where Self: Q ensures self.mm() == 2;
    fn z1(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub trait Tr { }
impl<X> Tr for S<X> { }
impl Q for u8 { }
pub trait V {
    proof fn lv(&self) where Self: U + Q ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
impl V for Z {
    proof fn lv(&self) { }
}
impl<X: Q> V for S<X> {
    proof fn lv(&self) { }
}
pub trait Q { }
} // verus!
