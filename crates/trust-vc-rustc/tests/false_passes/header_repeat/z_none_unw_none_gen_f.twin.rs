::verus_builtin_macros::verus!{
fn f<A>(a: A)  { opens_invariants_none(); no_unwind(); }
fn user() { f(1u8); assert(false); }
}
