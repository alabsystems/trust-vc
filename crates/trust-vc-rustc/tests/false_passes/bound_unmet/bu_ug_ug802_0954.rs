verus!{
pub struct Z { pub z: u8 }
impl Q for Z { }
impl Q for u8 { }
pub trait Tr { }
impl U for Z {
    proof fn lm0(&self) { }
}
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Tr { 2 }
    proof fn lm0(&self) where Self: Tr ensures self.mm() == 2;
}
pub trait Q { }
pub struct S<X> { pub x: X }
impl V for Z {
    proof fn lv(&self) { }
}
pub trait V {
    proof fn lv(&self) where Self: U + Tr ensures self.mm() == 2;
}
} // verus!
