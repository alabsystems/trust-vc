::verus_builtin_macros::verus!{
fn f()  { opens_invariants_none(); no_unwind(); }
fn user() { f(); assert(false); }
}
