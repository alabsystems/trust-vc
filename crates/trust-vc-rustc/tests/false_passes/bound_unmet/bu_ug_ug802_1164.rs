verus!{
impl<X> U for S<X> {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    fn z0(&self) -> (r: u8) { 2 }
}
impl V for Z {
    proof fn lv(&self) { }
}
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
pub trait Q { }
pub struct Z { pub z: u8 }
pub trait Tr { }
impl Q for u8 { }
pub struct S<X> { pub x: X }
impl<X: Tr> V for S<X> {
    proof fn lv(&self) { }
}
pub trait U {
    fn z0(&self) -> (r: u8) where Self: Tr ensures r == self.mm();
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X> Tr for S<X> { }
impl U for Z {
    fn z0(&self) -> (r: u8) { 2 }
}
} // verus!
