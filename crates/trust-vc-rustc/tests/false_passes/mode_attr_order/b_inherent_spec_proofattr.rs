::verus_builtin_macros::verus!{
pub struct S;
impl S {
    #[verifier::proof]
    spec fn s(&self) -> bool { false }
}
proof fn user() { let b = S.s(); assert(!b); }
}
