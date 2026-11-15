::verus_builtin_macros::verus!{
fn g() -> (r: (u64, u64)) ensures r.0 == 1 { (#[verifier::no_such_attribute] 1, 2) }
}
