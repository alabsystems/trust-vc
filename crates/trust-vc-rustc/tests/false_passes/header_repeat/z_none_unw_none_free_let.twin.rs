::verus_builtin_macros::verus!{
fn f()  { opens_invariants_none(); no_unwind(); let x = 1u8; }
fn user() { f();  }
}
