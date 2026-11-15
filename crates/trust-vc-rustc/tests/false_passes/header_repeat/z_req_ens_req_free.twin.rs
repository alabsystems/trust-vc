::verus_builtin_macros::verus!{
fn f()  { requires([true]); ensures([true]); }
fn user() { f();  }
}
