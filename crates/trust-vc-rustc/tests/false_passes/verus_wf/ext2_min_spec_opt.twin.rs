::verus_builtin_macros::verus!{
spec fn sid<A>(a: int) -> int { a }
fn f() { assert(sid::<u16>(1) == 1); }
}
