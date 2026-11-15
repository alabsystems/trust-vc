::verus_builtin_macros::verus!{
#[verus::internal(proof)]
proof fn p() ensures true { }
proof fn user() { p(); }
}
