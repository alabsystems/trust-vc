::verus_builtin_macros::verus!{
fn f()  { ensures([true]); no_unwind(); ensures([true]); let x = 1u8; }
fn user() { f();  }
}
