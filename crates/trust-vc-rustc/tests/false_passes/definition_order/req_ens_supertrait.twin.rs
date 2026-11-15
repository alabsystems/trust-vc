verus!{
pub trait T {
    spec fn f(&self) -> int;
}
pub trait U : T + Sized {
    proof fn p1(v: Self)
        ensures v.f() < 10;
    proof fn p2(&self) {
        Self::p1(*self);
    }
}
impl T for u32 {
    open spec fn f(&self) -> int { 50 }
}
impl U for u32 {
    proof fn p1(v: Self) {
    }
}
}
