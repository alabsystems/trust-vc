::verus_builtin_macros::verus!{
struct S { x: u8 }
fn f() { let s = S { x: 1 }; let a = s; proof { assume(true); } let b = s; }
}
