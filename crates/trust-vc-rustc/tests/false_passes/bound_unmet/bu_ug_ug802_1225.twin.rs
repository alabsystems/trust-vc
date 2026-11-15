verus!{
pub trait Q { } impl Q for Z { }
pub struct S<X> { pub x: X }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
impl<X> Tr for S<X> { }
impl Tr for Z { }
impl V for Z {
    proof fn lv(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Q { 2 }
    fn z0(&self) -> (r: u8) where Self: Q ensures r == self.mm();
}
pub trait V {
    proof fn lv(&self) where Self: U + Q ensures self.mm() == 2;
}
pub struct Z { pub z: u8 }
pub trait Tr { }
} // verus!
