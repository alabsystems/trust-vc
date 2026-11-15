pub trait Ext { }
verus!{
pub struct Z { pub z: u8 }
pub trait U {
    open spec fn mm(&self) -> u8 where Self: Ext { 2 }
    proof fn lm(&self) where Self: Ext ensures self.mm() == 2;
}
impl U for Z {
    proof fn lm(&self) { }
}
} // verus!
