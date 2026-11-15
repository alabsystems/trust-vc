::verus_builtin_macros::verus!{
fn t(i: u64) ensures ({ let ghost x = i; x == i }) { }
}
