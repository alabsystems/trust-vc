::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
fn user(x: NC) -> u8 { let a = x; let b = x; a.v }
}
