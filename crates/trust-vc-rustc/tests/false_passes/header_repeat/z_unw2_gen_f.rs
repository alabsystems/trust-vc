::verus_builtin_macros::verus!{
fn f<A>(a: A)  { no_unwind(); no_unwind(); }
fn user() { f(1u8); assert(false); }
}
