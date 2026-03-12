# guardgen/demo.py
from GenMonads.guardgen import gen_coq_guard

def run():
    example_groups = [
        (
            "x=3 && y=5  && sll(p1, l1) * sll(p2, l2) * store_tree(q, t)",
            [
                "p2 == null && q <> null",
                "(p2 == null && q <> null) || p1 != null",
                "!(p2 == null && q == null)",
                "!(p2 == null) && (q == null || p1 != null)",
                "r == null",  # should error
            ],
        ),
        (
            "sll(h, xs) * sll(t, ys)",
            [
                "h == null",
                "t != null && h == null",
                "!(h == null || t == null)",
            ],
        ),
        (
            "store_tree(r1, tr1) * store_tree(r2, tr2)",
            [
                "r1 == null || r2 != null",
                "!(r1 == null && r2 == null)",
            ],
        ),
        (
            "sll(a, l) * store_tree(b, t1) * store_tree(c, t2)",
            [
                "((a == null) || (b == null && c != null))",
                "!((a == null) || (b == null && c != null))",
            ],
        ),
        (
            "sll(cur, lh) * sllseg(head, cur, lseg) * store_tree(r, tr)",
            [
                "cur",
                "head == cur",
                "head != cur",
                "cur == null",  # ERROR: no sll(cur,...)
                "(head == cur) || r != null",
            ],
        ),
        (
            "x=1 && y=2",
            [
                "x == null",
            ],
        ),
        (
            """
sll(c, lc)   *    sllseg(a, b, lab)    *
sllseg(b, c, lbc) * store_tree(d, td)
""",
            [
                "a == b",
                "b != c",
                "b == a",
                "d == null",
                "(a == b) || !(b != c)",
            ],
        ),
        (
            """t != 0 && t -> next == 0 && t -> data == 0 && sllseg(x@pre,p, l1) * sll(p, l2) * sllseg(y, t, l3)""",
            [ 
                "p",
            ],
        ),
    ]

    for gi, (inv, conds) in enumerate(example_groups, 1):
        print(f"\n======= Invariant Group {gi} =======")
        print("INV:", inv.strip())
        for ci, cond in enumerate(conds, 1):
            print(f"\n-- Cond {ci}: {cond}")
            try:
                print(gen_coq_guard(inv, cond))
            except ValueError as e:
                print("ERROR:", e)

if __name__ == "__main__":
    run()
