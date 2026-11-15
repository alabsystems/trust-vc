::verus_builtin_macros::verus!{
spec fn s(x: nat) -> nat decreases #[verifier::no_such_attribute] x { if x == 0 { 0 } else { s((x - 1) as nat) } }
}
