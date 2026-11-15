::verus_builtin_macros::verus!{
proof fn f()  { requires([true]); }
proof fn user() { f(); assert(false); }
}
