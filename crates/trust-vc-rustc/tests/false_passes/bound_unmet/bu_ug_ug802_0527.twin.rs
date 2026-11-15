verus!{
pub trait Q { } impl Tr for Z { } impl Q for Z { }
pub struct S<X> { pub x: X }
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
impl<X: Q> Tr for S<X> { }
pub trait Tr { }
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl V for Z {
    proof fn lv(&self) { }
}
impl Q for u8 { }
impl U for Z {
    proof fn lm0(&self) { }
}
} // verus!
