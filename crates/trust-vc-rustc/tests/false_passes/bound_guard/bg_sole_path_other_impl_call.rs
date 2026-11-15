verus!{
pub struct A { pub a: u8 }
pub struct B { pub b: u8 }
pub trait Tr { fn x(&self) -> (r: u8); }
pub trait U: Tr {
    open spec fn mm(&self) -> u8 { 2 }
    proof fn lm(&self) ensures self.mm() == 2;
    proof fn dm(&self) { }
}
impl Tr for A { fn x(&self) -> (r: u8) { let _q = (B { b: 1 }).x(); 1 } }
impl U for B {
    proof fn lm(&self) { }
}
impl Tr for B { fn x(&self) -> (r: u8) { 1 } }
} // verus!
