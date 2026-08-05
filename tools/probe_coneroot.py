"""The two cone transports needed to lift `gcopies_mem_GX` to `d1 > 0`.

To turn the guarded copies block into an ITERATED ROOT-LIFT graft recursion
(probe_gcopieshi's (H3)) the only missing fact is that "in the row-1 cone of
the whole copies block's root" is the same as "in the row-1 cone of one's own
copy root".  Reusing `Gtrans.gexp_chain_inversion` (which does NOT need
`0 < j0`) that splits into

  (T1) le1_seg_rebase — re-basing the window does not change its root cone:
        le1 R p (p+q)  <->  le1 (shiftl0 c (seg R p (L+1))) 0 q     (q < L)

  (T2) gexp_cone_mir_root — the j0 = 0 case of `Lcone.gexp_cone_mir`:
        le1 (gexp B 0 L d0 d1 n) 0 (k*L+q)  <->  le1 B 0 q

       under  hup : forall 0 < l <= L, B[0].0 < B[l].0
              hd0pos, hd0e : B[L].0 = B[0].0 + d0
              hd1pos, hlp : le1 B 0 L

`hlp` (the blocked column is in the block root's row-1 cone) is what fails in
probe_gcopieshi's surviving random counterexamples, and it is exactly what a
row-2 blocker supplies (`p = parent R 2 x` gives `le2 R p x`, hence `le1`).
`hd1pos` is needed for the copy roots themselves (`q' = 0`).
"""
import sys
import random
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def seg(R, a, L):
    return [tuple(R[j]) for j in range(a, a + L)]


def shiftl0(c, X):
    return [(q[0] - c, q[1], q[2]) for q in X]


def gcopy(R, r, L, d0, d1, k):
    return [(R[j][0] + k * d0,
             R[j][1] + (k * d1 if trio.is_ancestor(R, 1, r, j) else 0),
             R[j][2])
            for j in range(r, r + L)]


def gcopies(R, r, L, d0, d1, n):
    out = []
    for k in range(n):
        out += gcopy(R, r, L, d0, d1, k)
    return out


def le1(X, a, b):
    return a < len(X) and b < len(X) and trio.is_ancestor(X, 1, a, b)


COLS = [(a, b, c) for a in range(1, 6) for b in range(4) for c in range(2)]
rnd = random.Random(517)

tot = Counter()
bad = Counter()
ex = {}


def note(key, ok, data):
    tot[key] += 1
    if not ok:
        bad[key] += 1
        ex.setdefault(key, data)


N = 120000
for _ in range(N):
    R = [rnd.choice(COLS) for _ in range(rnd.randrange(3, 8))]
    p = rnd.randrange(0, len(R) - 1)
    L = rnd.randrange(1, len(R) - p)
    if p + L >= len(R):
        continue
    c = R[p][0]
    # hup: the window is STRICTLY deeper than the block root, through the
    # blocked column p+L inclusive
    if any(R[j][0] <= c for j in range(p + 1, p + L + 1)):
        continue
    d0 = R[p + L][0] - c
    if d0 <= 0:
        continue
    B = shiftl0(c, seg(R, p, L + 1))

    # (T1) re-basing preserves the root cone
    ok1 = all(le1(R, p, p + q) == le1(B, 0, q) for q in range(L))
    note('T1', ok1, (R, p, L))

    # (T1') and hence the copies block re-bases
    d1 = rnd.randrange(0, 4)
    n = rnd.randrange(0, 4)
    note('T1copies',
         shiftl0(c, gcopies(R, p, L, d0, d1, n)) == gcopies(B, 0, L, d0, d1, n),
         (R, p, L, d0, d1, n))

    # (T2) root-cone transport for the re-based block
    hlp = le1(B, 0, L)
    key = 'T2' + ('/hlp' if hlp else '/nolp') + ('/d1>0' if d1 > 0 else '/d1=0')
    X = gcopies(B, 0, L, d0, d1, n)
    ok2 = True
    for k in range(n):
        for q in range(L):
            if le1(X, 0, k * L + q) != le1(B, 0, q):
                ok2 = False
    note(key, ok2, (R, p, L, d0, d1, n, B))

print(f"{'case':16s} {'samples':>9s} {'viol':>8s}")
for k in sorted(tot):
    print(f"{k:16s} {tot[k]:9d} {bad[k]:8d}")
for k, e in sorted(ex.items()):
    print(f"  ex {k}: {e}")
