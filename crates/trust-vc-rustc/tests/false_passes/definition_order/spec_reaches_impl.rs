verus!{
trait A {
    spec fn a(&self) -> bool;
    proof fn foo(&self)
        ensures self.a();
}
trait B: A {
    spec fn b(&self) -> bool;
}
impl A for bool {
    spec fn a(&self) -> bool { true }
    proof fn foo(&self) { }
}
impl B for bool {
    spec fn b(&self) -> bool { self.a() || false }
}
}
