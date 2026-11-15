::verus_builtin_macros::verus!{
uninterp spec fn u() -> bool;
fn f() -> u8 { let x: u8 = 1; proof { } x }
}
