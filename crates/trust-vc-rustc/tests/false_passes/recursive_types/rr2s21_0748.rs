::verus_builtin_macros::verus!{
pub struct S0 { pub f0: (u8, i32), pub f1: u8, f2: &'static S0 }
proof fn user() { }
}
