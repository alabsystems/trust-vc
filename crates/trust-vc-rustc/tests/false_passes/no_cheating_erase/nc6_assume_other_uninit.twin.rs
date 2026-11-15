::verus_builtin_macros::verus!{
proof fn g() { assume(true); }
fn f() -> u8 { let x: u8 = 1; x }
}
