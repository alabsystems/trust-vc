pub trait Sub: Q { }
verus!{
pub trait Q {
    spec fn v(&self) -> u8;
    proof fn qm(&self) ensures self.v() == 2;
}
pub proof fn f<X: Sub + Q>(x: X) ensures x.v() == 2 { x.qm(); }
} // verus!
