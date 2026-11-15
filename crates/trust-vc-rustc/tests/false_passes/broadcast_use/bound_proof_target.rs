::verus_builtin_macros::verus!{
proof fn l() ensures true { }
proof fn test() { broadcast use l; }
}
