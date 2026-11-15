::verus_builtin_macros::verus!{
fn f() no_unwind { }
fn user() { f(); assert(false); }
}
