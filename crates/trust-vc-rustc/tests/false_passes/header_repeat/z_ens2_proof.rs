::verus_builtin_macros::verus!{
proof fn f()  { ensures([true]); ensures([true]); }
proof fn user() { f();  }
}
