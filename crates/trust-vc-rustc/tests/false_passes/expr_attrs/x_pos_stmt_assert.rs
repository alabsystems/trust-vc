::verus_builtin_macros::verus!{
fn g(x: u64) requires x == 1 { #[verifier::no_such_attribute] assert(x == 1); }
}
