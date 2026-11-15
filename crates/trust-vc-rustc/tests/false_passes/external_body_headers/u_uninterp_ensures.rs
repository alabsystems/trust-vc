::verus_builtin_macros::verus!{
pub uninterp spec fn f(x: int) -> bool ensures false;
proof fn user() { assert(f(1) == f(1)); }
}
