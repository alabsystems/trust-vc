::verus_builtin_macros::verus!{
spec fn s(x: nat) -> nat decreases x { if x == 0 { 0 } else { s((x - 1) as nat) } }
}
