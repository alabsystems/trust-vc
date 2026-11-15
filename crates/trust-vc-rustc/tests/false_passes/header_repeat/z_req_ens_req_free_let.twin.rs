::verus_builtin_macros::verus!{
fn f()  { requires([true]); ensures([true]); let x = 1u8; }
fn user() { f();  }
}
