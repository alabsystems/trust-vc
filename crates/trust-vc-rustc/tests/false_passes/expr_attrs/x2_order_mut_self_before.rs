::verus_builtin_macros::verus!{
struct S { a: u64 }
impl S { fn m(mut self) { let y = #[verifier::no_such_attribute] 1u64; } }
}
