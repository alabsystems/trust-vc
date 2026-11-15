::verus_builtin_macros::verus!{
#[verifier::opaque] spec fn s() -> bool { true }
fn f() {
    ::verus_builtin::reveal_hide_({ #[verus::internal(reveal_fn)] fn __VERUS_REVEAL_INTERNAL__() { ::verus_builtin::reveal_hide_internal_path_(s) } __VERUS_REVEAL_INTERNAL__ }, 1);
}
}
