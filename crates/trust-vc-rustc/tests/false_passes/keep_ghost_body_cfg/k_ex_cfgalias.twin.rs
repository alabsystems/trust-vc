::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
}
type T = NC;
::verus_builtin_macros::verus!{
fn user(x: T) -> (T, T) { (x, x) }
}
