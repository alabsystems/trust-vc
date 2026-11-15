::verus_builtin_macros::verus!{
fn f() { let c = |x: u64| x; let y = #[verifier::no_such_attribute] 1u64; }
}
