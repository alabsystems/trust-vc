::verus_builtin_macros::verus!{
#[allow(dead_code)]
pub trait T { fn f(&self) -> (r: u8) ensures r == 1; }
}
