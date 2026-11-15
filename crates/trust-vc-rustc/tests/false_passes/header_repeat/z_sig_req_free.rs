::verus_builtin_macros::verus!{
fn f() requires true { requires([true]); }
fn user() { f();  }
}
