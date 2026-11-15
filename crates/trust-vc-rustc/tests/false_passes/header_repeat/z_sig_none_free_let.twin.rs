::verus_builtin_macros::verus!{
fn f() opens_invariants none { let x = 1u8; }
fn user() { f();  }
}
