::verus_builtin_macros::verus!{
fn f() opens_invariants none { opens_invariants_none(); }
fn user() { f();  }
}
