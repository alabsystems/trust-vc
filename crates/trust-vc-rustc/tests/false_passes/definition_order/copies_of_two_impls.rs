verus!{
pub struct A { pub a: u8 }
pub struct B;
pub trait Tr {
    spec fn lim(&self) -> u8;
    open spec fn s(&self) -> bool { self.lim() > 0 }
    fn x(&self) -> (r: u8) ensures r == self.lim();
    fn run(&self) -> u8 { self.x() }
}
impl Tr for A {
    fn x(&self) -> (r: u8) { self.a }
    open spec fn lim(&self) -> u8 { self.a }
}
impl Tr for B {
    fn x(&self) -> (r: u8) { call_a() }
    open spec fn lim(&self) -> u8 { 1 }
}
fn call_a() -> (r: u8) ensures r == 1 { let r = (A { a: 1 }).x(); r }
}
