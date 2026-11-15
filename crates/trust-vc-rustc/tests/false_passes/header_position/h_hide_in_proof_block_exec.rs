::verus_builtin_macros::verus!{
spec fn s(x: int) -> bool { x > 0 }
fn g() { proof { hide(s); } }
}
