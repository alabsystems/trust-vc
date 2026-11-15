::verus_builtin_macros::verus!{
fn e() -> u64 { 1 }
#[verifier::external_body]
fn f() -> u64 { e() }
}
