::verus_builtin_macros::verus!{
fn f(x: u64) -> (r: u64) requires x < 10 ensures r == x + 1 { let y = #[verifier::invalid_trigger_attribute] (x + 1); y }
}
