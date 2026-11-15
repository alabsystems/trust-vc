pub trait Sub: Q { }
verus!{
pub trait Q { }
pub open spec fn g<X: Q>(x: X) -> u8 { 2 }
pub fn f<X: Sub + Q>(x: X) -> (r: u8) ensures r == g(x) { 2 }
} // verus!
