::verus_builtin_macros::verus!{
mod m { #[verifier::opaque] pub open spec fn f() -> bool { true } }
proof fn test() { reveal(m::f); assert(m::f()); }
}
