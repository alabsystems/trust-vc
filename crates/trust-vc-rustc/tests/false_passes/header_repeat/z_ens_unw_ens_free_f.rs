::verus_builtin_macros::verus!{
fn f()  { ensures([true]); no_unwind(); ensures([true]); }
fn user() { f(); assert(false); }
}
