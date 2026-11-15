// A proof block that stands for a value is ghost code: the tail of an `if`
// branch or of a block, a `let` initializer, a call argument. Each is read as
// a `ghost` statement whose value is `()`.
verus! {

proof fn lemma(x: u64)
    ensures
        x >= 0,
{
}

fn e(u: ()) {
}

fn branches(b: bool, x: u64) -> (r: u64)
    ensures
        r == x,
{
    if b {
        proof {
            lemma(x);
            let y = x + 1;
            assert(y > x);
        }
    } else {
        proof {
            assert(x >= 0);
        }
    }
    x
}

fn initializers(x: u64) {
    let u = {
        proof {
            assert(x == x);
        }
    };
    let v = proof {
        lemma(x);
    };
    e(proof {
        assert(x >= 0);
    });
}

} // verus!
