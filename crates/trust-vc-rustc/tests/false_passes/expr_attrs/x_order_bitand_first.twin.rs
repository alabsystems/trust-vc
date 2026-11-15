::verus_builtin_macros::verus!{
fn f(a: bool, b: bool) { let c = a && b; let y = #[verifier::no_such_attribute] 1u64; }
}
