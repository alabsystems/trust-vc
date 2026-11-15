// Loops: the condition with its statements, the header clauses in Verus's
// order, `break` and `continue` naming their loop, and the loop settings.
verus! {

fn count(n: u32) -> (r: u32)
    requires
        n <= 100,
    ensures
        r == n,
{
    let mut i: u32 = 0;
    let mut steps: u32 = 0;
    while {
        steps = steps + 1;
        i < n
    }
        invariant
            i <= n,
            n <= 100,
            steps == i,
        decreases n - i
    {
        i = i + 1;
    }
    i
}

fn search(b: bool) {
    let mut i: u8 = 0;
    'outer: loop
        invariant_except_break
            i <= 10,
        ensures
            i <= 10,
        decreases 10 - i
    {
        if i == 10 {
            break;
        }
        i = i + 1;
        #[verifier::loop_isolation(false)]
        while b
            invariant
                i <= 10,
            decreases 0int
        {
            break 'outer;
        }
        if b {
            continue 'outer;
        }
    }
}

} // verus!
