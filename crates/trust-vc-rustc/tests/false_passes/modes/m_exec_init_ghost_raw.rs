::verus_builtin_macros::verus!{
fn f() {
    #[verus::internal(spec)] let x: u64 = 5;
}
}
