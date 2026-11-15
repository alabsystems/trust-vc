::verus_builtin_macros::verus!{
pub trait T { fn d(&self) -> (r: u8) ensures r == 1 { 1 } }
mod m { pub struct S; impl crate::T for S {} }
}
