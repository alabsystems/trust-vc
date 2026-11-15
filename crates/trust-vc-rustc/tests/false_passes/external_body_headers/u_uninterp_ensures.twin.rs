::verus_builtin_macros::verus!{
pub uninterp spec fn f(x: int) -> bool;
proof fn user() { assert(f(1) == f(1)); }
}
