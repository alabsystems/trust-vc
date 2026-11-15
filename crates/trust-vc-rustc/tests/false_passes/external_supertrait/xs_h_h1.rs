pub trait Sub: Q { }
verus!{
pub trait Q { }
pub open spec fn g<X: Q>(x: X) -> u8 { 2 }
pub proof fn f<X: Sub>(x: X) ensures g(x) == 2 { }
} // verus!
