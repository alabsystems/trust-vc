::verus_builtin_macros::verus!{
proof fn l() ensures true { }
proof fn test() { reveal(l); }
}
