::verus_builtin_macros::verus!{
fn f<A>(a: A) opens_invariants none { }
fn user() { f(1u8);  }
}
