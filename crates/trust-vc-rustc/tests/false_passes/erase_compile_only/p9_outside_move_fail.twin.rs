struct S { x: u8 }
fn e() { let s = S { x: 1 }; let a = s; let b = s; }
::verus_builtin_macros::verus!{
fn f() { assert(1 + 1 == 2); }
}
