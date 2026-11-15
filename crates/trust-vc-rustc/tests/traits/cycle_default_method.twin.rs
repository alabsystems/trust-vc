::verus_builtin_macros::verus!{
trait T: Sized { proof fn g() ensures true { f::<Self>(); } }
proof fn f<A: T>() ensures true { A::g(); }
}
