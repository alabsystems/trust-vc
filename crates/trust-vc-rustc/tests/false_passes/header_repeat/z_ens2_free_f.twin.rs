::verus_builtin_macros::verus!{
fn f()  { ensures([true]); }
fn user() { f(); assert(false); }
}
