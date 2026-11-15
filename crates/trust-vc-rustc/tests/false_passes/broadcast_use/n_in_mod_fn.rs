::verus_builtin_macros::verus!{
mod m { #[verifier::opaque] pub open spec fn f() -> bool { true }
pub fn test() { broadcast use f; assert(f()); } }
}
