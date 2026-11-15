::verus_builtin_macros::verus!{
proof fn f()  { requires([true]); ensures([true]); }
proof fn user() { f(); assert(false); }
}
