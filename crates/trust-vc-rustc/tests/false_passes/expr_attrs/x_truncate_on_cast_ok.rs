::verus_builtin_macros::verus!{
fn f(x: u64) -> (r: u8) { let y = #[verifier::truncate] (x + 0); y as u8 }
}
