::verus_builtin_macros::verus!{
pub struct S<A> { pub a: A }
impl<A> S<A> { fn f(&self) requires true { } }
fn user(s: &S<u8>) { s.f();  }
}
