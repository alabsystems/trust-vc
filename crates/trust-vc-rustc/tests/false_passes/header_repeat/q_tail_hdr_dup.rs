::verus_builtin_macros::verus!{
fn f() { requires([true]); requires([false]); }
fn user() { f(); }
}
