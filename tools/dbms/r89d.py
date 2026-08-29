# -*- coding: utf-8 -*-
"""**R89 その 4 —— (c) `j0` は `b, c` に依存するか。**

`CoreCap` の `∀ b c` が「見かけだけ」なら証明は軽くなる。そこで固定した
`(M, v, z, t)` について `(b, c)` を振り、次の 3 つを別々に測る:

  (c1) 分岐（noparent / copy）が `(b,c)` で変わるか
  (c2) copy に落ちたときの `j0` の値が `(b,c)` で変わるか
  (c3) **二分（j0=0 か j0>=1 か）**が `(b,c)` で変わるか  ← 証明の場合分けに効くのはこれ
  (c4) `j0 >= 1` のとき `j0` は `(b,c)` に依らず「行 0 の親 p1」に等しいか
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r89 import lift1, shape, cap
from r89b import rowparent0

def run(DS, BS, CS, VS, ZS, TS, CAPB, CAPC, LS, label):
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    c1 = Counter(); c2 = Counter(); c3 = Counter(); c4 = Counter()
    ex = {}
    t0 = time.time()
    for L in LS:
        for Mt in itertools.product(COL, repeat=L):
            M = list(Mt)
            for v in VS:
                for z in ZS:
                    for t in TS:
                        brs, j0s, dic = set(), set(), set()
                        for b in CAPB:
                            for c in CAPC:
                                S = lift1([(0, v, z)] + cap(M, b, c), t)
                                j1 = len(S) - 1
                                br, j0, i1, d0, d1 = shape(S)
                                brs.add(br)
                                if br == 'copy':
                                    j0s.add(j0); dic.add(j0 == 0)
                                    p1 = rowparent0(S, j1)
                                    if j0 >= 1:
                                        c4['j0=p1' if j0 == p1 else 'j0!=p1'] += 1
                        c1['const' if len(brs) == 1 else f'varies{len(brs)}'] += 1
                        if j0s:
                            c2['const' if len(j0s) == 1 else f'varies{len(j0s)}'] += 1
                            c3['const' if len(dic) == 1 else 'FLIPS'] += 1
                            if len(dic) > 1:
                                ex.setdefault('flip', (M, v, z, t, sorted(j0s)))
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s)')
    for nm, cc in (('c1 分岐', c1), ('c2 j0 の値', c2),
                   ('c3 二分 j0=0/j0>=1', c3), ('c4 j0>=1 なら j0=p1 か', c4)):
        print(f'  -- {nm} --')
        for k in sorted(cc):
            print(f'     {k:14s} {cc[k]:10d}')
    for k in sorted(ex):
        print(f'  ex {k}: {ex[k]}')
    print()

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--L', type=int, default=3)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2), (0, 1), (0, 1, 2), (0, 1), (0, 1, 2),
        (0, 1, 2, 3), (0, 1, 2), tuple(range(1, a.L + 1)), f'R89d (c) |M|<={a.L}')
