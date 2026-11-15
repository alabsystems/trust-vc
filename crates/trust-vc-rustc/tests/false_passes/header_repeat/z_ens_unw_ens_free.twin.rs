::verus_builtin_macros::verus!{
fn f()  { ensures([true]); no_unwind(); }
fn user() { f();  }
}
