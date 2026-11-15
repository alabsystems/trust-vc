verus!{
pub struct A { pub a: u8 }
pub trait Tr {
    spec fn ok(&self) -> bool;
    fn chk(&self) -> (r: bool) ensures r == self.ok();
    fn run(&self) -> (r: bool) { self.chk() }
}
impl Tr for A {
    open spec fn ok(&self) -> bool { true }
    fn chk(&self) -> (r: bool) ensures r == self.ok() { true }
}
}
