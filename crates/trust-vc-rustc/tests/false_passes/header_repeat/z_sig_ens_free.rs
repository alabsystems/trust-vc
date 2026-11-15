::verus_builtin_macros::verus!{
fn f() ensures true { ensures([true]); }
fn user() { f();  }
}
