::verus_builtin_macros::verus!{
fn f<A>(a: A)  { ensures([true]); no_unwind(); }
fn user() { f(1u8);  }
}
