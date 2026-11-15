::verus_builtin_macros::verus!{
#[verus::internal(spec)] #[verus::internal(returns(exec))]
fn f(x: u64) -> u64 { x }
}
