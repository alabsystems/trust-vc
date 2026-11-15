::verus_builtin_macros::verus!{
pub open spec fn foo() -> bool
  recommends
  {
      true
  }

proof fn test() { broadcast use foo;
    assert(foo());
}
}
