::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
fn user<A>(x: NC, a: A) -> u8 { let p = x; let q = x; p.v }
}
