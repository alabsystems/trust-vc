::verus_builtin_macros::verus!{
proof fn t(i: int) { assert({ let tracked x = i; x == i }); }
}
