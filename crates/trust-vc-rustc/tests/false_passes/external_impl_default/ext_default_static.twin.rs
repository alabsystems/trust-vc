::verus_builtin_macros::verus!{
pub trait T { fn f() -> (r: u8) ensures r == 1 { 1 } }
pub struct S;
}
impl T for S { }
::verus_builtin_macros::verus!{
fn user() { let r = 1u8; assert(r == 1); }
}
