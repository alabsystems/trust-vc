::verus_builtin_macros::verus!{
struct S { x: u8 }
proof fn g() { admit(); }
fn f() { let s = S { x: 1 }; let a = s; }
}
