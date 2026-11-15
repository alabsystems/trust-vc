::verus_builtin_macros::verus!{
uninterp spec fn u() -> bool;
mod m { pub struct S { x: u8 }
 pub fn f() { let s = S { x: 1 }; let a = s; let b = s; } }
}
