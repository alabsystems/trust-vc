::verus_builtin_macros::verus!{
fn f()  { no_unwind(); no_unwind(); let x = 1u8; }
fn user() { f(); assert(false); }
}
