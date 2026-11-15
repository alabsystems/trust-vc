::verus_builtin_macros::verus!{
proof fn f()  { requires([true]); ensures([true]); requires([true]); }
proof fn user() { f();  }
}
