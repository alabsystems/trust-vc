::verus_builtin_macros::verus!{
spec fn s(a: bool) -> bool { a }
fn foo() { reveal_with_fuel(s, 0); }
}
