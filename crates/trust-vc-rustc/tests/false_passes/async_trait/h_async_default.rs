::verus_builtin_macros::verus!{
pub trait T {
    async fn f(&self) -> u8 { 1 }
    fn g(&self) -> (r: u8) ensures r == 1 { 1 }
}
fn user() { assert(1 + 1 == 2); }
}
