::verus_builtin_macros::verus!{
fn f<A>(a: A)  { requires([true]); ensures([true]); requires([true]); }
fn user() { f(1u8);  }
}
