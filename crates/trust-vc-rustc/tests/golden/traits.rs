// A trait method declaration, an implementation that inherits its clauses,
// a default method, and calls resolved statically, through an instance and
// through the declaration.
verus! {

trait T {
    spec fn val(&self) -> int;
    fn get(&self) -> (r: u8)
        requires self.val() < 100,
        ensures r as int == self.val();
    spec fn twice(&self) -> int { 2 * self.val() }
}

struct S { x: u8 }

impl T for S {
    spec fn val(&self) -> int { self.x as int }
    fn get(&self) -> (r: u8)
        ensures r == self.x
    {
        self.x
    }
}

fn concrete(s: &S)
    requires s.x < 10,
{
    let r = s.get();
    assert(r == s.x);
    assert(s.twice() == 2 * s.x);
}

fn generic<A: T>(a: &A)
    requires a.val() == 5,
{
    let r = a.get();
    assert(r == 5);
}

} // verus!
