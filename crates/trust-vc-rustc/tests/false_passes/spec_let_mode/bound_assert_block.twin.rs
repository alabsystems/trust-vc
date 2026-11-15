::verus_builtin_macros::verus!{
proof fn t(i: int) { assert({ let ghost x = i; x == i }); }
}
