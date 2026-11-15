::verus_builtin_macros::verus!{
fn f() requires true { }
fn user() { f(); assert(false); }
}
