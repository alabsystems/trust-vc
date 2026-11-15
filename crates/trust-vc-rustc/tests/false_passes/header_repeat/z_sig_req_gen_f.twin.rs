::verus_builtin_macros::verus!{
fn f<A>(a: A) requires true { }
fn user() { f(1u8); assert(false); }
}
