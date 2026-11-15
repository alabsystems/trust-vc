::verus_builtin_macros::verus!{
struct S { x: u8 }
#[verifier::external_body]
fn e() { let s = S { x: 1 }; let a = s; let b = s; }
proof fn p() { let x: int = 1; x = 2; }
}
