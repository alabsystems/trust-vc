::verus_builtin_macros::verus!{
proof fn g() { assume(true); }
struct S { x: u8 }
fn consume(s: S) {}
fn f() {
    let s = S { x: 1 };
    consume(s);
    consume(s);
}

}
