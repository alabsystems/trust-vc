::verus_builtin_macros::verus!{
fn f()  { requires([true]); ensures([true]); requires([true]); }
fn user() { f(); assert(false); }
}
