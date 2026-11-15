::verus_builtin_macros::verus!{
fn g(x: u64) -> (r: u64) ensures r >= 1 { match x { 0 => #[verifier::no_such_attribute] 1, _ => 2 } }
}
