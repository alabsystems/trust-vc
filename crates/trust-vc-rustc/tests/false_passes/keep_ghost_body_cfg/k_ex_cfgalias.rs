::verus_builtin_macros::verus!{
pub struct NC { pub v: u8 }
}
#[cfg(verus_keep_ghost_body)] type T = NC; #[cfg(not(verus_keep_ghost_body))] type T = u8;
::verus_builtin_macros::verus!{
fn user(x: T) -> (T, T) { (x, x) }
}
