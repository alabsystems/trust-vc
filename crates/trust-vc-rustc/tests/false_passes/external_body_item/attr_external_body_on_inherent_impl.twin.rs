::verus_builtin_macros::verus!{
pub struct S;
#[allow(dead_code)]
impl S { fn f(&self) -> (r: u8) ensures r == 1 { 1 } }
}
