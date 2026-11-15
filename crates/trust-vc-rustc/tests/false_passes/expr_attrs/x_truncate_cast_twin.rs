::verus_builtin_macros::verus!{
fn f(x: u64) -> (r: u8) { #[verifier::truncate] ((x + 0) as u16) as u8 }
}
