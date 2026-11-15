verus!{
impl Q for u8 { }
impl V for Z {
    proof fn lv(&self) { }
}
impl<X: Q> Tr for S<X> { }
pub trait Q { } impl Tr for Z { } impl Q for Z { }
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm0(&self) { }
}
pub struct Z { pub z: u8 }
pub trait U {
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
}
pub struct S<X> { pub x: X }
impl Tr for u8 { }
pub trait Tr { }
} // verus!
