::verus_builtin_macros::verus!{
fn f(x: u64) requires x == 5 { assert(x == 5 && (#[verifier::no_such_attribute] (x > 1))); }
}
