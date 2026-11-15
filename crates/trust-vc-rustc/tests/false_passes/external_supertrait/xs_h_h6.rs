pub trait Sub: Q { }
verus!{
pub trait Q { }
pub proof fn f<X: Sub>(x: X) ensures 1 + 1 == 2 { }
} // verus!
