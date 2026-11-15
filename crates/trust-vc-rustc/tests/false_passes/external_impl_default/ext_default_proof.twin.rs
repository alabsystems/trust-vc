::verus_builtin_macros::verus!{
pub trait T { proof fn l(&self) ensures 1 + 1 == 2 { } }
pub struct S;
}
impl T for S { }
::verus_builtin_macros::verus!{
proof fn user(s: &S) { }
}
