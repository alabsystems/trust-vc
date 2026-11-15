::verus_builtin_macros::verus!{
#[verus::internal(exec)]
proof fn p() ensures true { }
proof fn user() { p(); }
}
