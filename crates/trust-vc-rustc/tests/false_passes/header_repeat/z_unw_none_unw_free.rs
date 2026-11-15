::verus_builtin_macros::verus!{
fn f()  { no_unwind(); opens_invariants_none(); no_unwind(); }
fn user() { f();  }
}
