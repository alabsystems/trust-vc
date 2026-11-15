::verus_builtin_macros::verus!{
#[derive(Clone, Copy)]
pub struct NC { pub v: u8 }
fn user(x: NC) -> (NC, NC) { (x, x) }
}
