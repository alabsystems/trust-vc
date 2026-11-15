use verus_builtin::*; use verus_builtin_macros::*;
::verus_builtin_macros::verus!{
fn foo(x: u32) -> u32 { x / 2 }
}
