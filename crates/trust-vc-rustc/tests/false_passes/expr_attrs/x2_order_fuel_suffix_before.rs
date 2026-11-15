::verus_builtin_macros::verus!{
spec fn t() -> int { 1 }
proof fn p() { reveal_with_fuel(t, 1u32); let a = #[verifier::no_such_attribute] 1int; }
}
