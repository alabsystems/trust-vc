::verus_builtin_macros::verus!{
proof fn t(i: int) requires ({ let tracked x = i; x > 0 }) { }
}
