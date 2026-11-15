::verus_builtin_macros::verus!{
fn t(i: u64) ensures ({ let tracked x = i; x == i }) { }
}
