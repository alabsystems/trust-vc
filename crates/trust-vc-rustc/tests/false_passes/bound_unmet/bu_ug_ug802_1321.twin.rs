verus!{
pub trait Q { } impl Tr for Z { } impl Q for Z { }
pub struct S<X> { pub x: X }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
impl Q for u8 { }
impl V for Z {
    proof fn lv(&self) { }
}
pub struct Z { pub z: u8 }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait Tr { }
} // verus!
