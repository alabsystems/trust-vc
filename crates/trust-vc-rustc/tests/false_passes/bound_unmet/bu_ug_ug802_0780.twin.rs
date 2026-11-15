verus!{
pub trait Tr { } impl Tr for Z { }
impl Q for Z { }
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Q { }
impl U for Z {
    proof fn lm0(&self) { }
}
impl V for Z {
    proof fn lv(&self) { }
}
pub struct S<X> { pub x: X }
impl<X: Q> Tr for S<X> { }
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
} // verus!
