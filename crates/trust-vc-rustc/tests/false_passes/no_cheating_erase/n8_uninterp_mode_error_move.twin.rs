::verus_builtin_macros::verus!{
struct S { x: u8 }
uninterp spec fn u() -> bool;
fn g() -> u8 { let x: u8 = 1; x }
fn f() { let s = S { x: 1 }; let a = s; let b = s; }
}
