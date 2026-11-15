::verus_builtin_macros::verus!{
fn f()  { no_unwind(); opens_invariants_none(); let x = 1u8; }
fn user() { f(); assert(false); }
}
