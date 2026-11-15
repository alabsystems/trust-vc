verus!{
impl Q for u8 { }
pub trait U {
    fn z1(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Q { }
impl V for Z {
    proof fn lv(&self) { }
}
pub struct S<X> { pub x: X }
pub trait Tr { }
pub struct Z { pub z: u8 }
impl Tr for u8 { }
impl<X> Tr for S<X> { }
impl U for Z {
    proof fn lm0(&self) { }
    fn z1(&self) -> (r: u8) { 2 }
}
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
} // verus!
