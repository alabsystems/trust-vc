::verus_builtin_macros::verus!{
mod m { #[verifier::opaque] pub closed spec fn f() -> bool { true } }
fn test() { reveal(m::f); }
}
