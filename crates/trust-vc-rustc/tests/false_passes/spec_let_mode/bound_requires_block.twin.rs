::verus_builtin_macros::verus!{
proof fn t(i: int) requires ({ let x = i; x > 0 }) { }
}
