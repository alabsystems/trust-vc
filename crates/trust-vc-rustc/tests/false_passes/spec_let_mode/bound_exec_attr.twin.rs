::verus_builtin_macros::verus!{
spec fn f(i: int) -> int { #[verus::internal(proof)] let x = i; x }
}
