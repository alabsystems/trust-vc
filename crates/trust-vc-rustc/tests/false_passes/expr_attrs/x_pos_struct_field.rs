::verus_builtin_macros::verus!{
struct S { a: u64 }
fn g() -> (s: S) ensures s.a == 1 { S { a: #[verifier::no_such_attribute] 1 } }
}
