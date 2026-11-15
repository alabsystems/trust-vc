::verus_builtin_macros::verus!{
fn f(x: u64) -> (r: u64) requires x < 10 ensures r == x + 1 { let y = #[verifier::auto_ext_equal(assert)] (x + 1); y }
}
