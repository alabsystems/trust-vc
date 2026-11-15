verus!{
pub trait Q { } impl Tr for Z { } impl Q for Z { }
impl U for Z {
    proof fn lm0(&self) { }
    proof fn lm1(&self) { }
}
pub struct S<X> { pub x: X }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    proof fn lm1(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Tr { }
pub struct Z { pub z: u8 }
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl V for Z {
    proof fn lv(&self) { }
}
impl<X> Tr for S<X> { }
} // verus!
