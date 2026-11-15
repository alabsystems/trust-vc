::verus_builtin_macros::verus!{
fn f<A>(a: A)  { no_unwind(); opens_invariants_none(); }
fn user() { f(1u8); assert(false); }
}
