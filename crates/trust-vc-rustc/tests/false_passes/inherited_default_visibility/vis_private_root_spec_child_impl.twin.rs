::verus_builtin_macros::verus!{
pub trait T { open spec fn d(&self) -> int { 1 } }
mod m { pub struct S; impl crate::T for S {} }
}
