::verus_builtin_macros::verus!{
pub trait T { open spec fn d(&self) -> int { 1 } }
pub struct S;
}
impl T for S { }
::verus_builtin_macros::verus!{
proof fn user(s: S) { assert(s.d() == 1); }
}
