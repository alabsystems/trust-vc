::verus_builtin_macros::verus!{
proof fn g() { assume(true); }
fn f() { let x: u8; x = 5; x = 7; }
}
