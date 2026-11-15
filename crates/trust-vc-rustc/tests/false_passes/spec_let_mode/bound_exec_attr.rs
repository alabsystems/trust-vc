::verus_builtin_macros::verus!{
spec fn f(i: int) -> int { #[verus::internal(exec)] let x = i; x }
}
