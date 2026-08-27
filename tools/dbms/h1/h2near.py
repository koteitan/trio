# -*- coding: utf-8 -*-
"""目標 T に**近い**標準形 B（|conv3 B| == |T| で食い違いが少ないもの）をさがす。

`imgfast.search2` と同じ木を歩くが、`Q == T` の枝だけでなく
「長さが同じで食い違いが k 本以下」のものを集める。族 β の教師データ用。
"""
import sys
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3
from rows3 import b2d3
from core import expand, isstd, show, flat
from imgfast import lo_state, hi_state, lcp


def nearmiss(A, m, f=b2d3, T=None, SL=6, nodecap=200000, Lmax=None,
             uselo=True, maxdiff=6, topk=20):
    if T is None:
        T = tuple(expand(f(A), m))
    LT = len(T)
    if Lmax is None:
        Lmax = (3 * LT + 1) // 2
    lo = tuple(expand(A, max(m - 1, 1))) if (uselo and m > 1) else None
    U = tuple(A)
    flo = flat(lo) if lo is not None else None
    fhi = flat(U) if U is not None else None
    out, cnt, hitcap = [], [0], [False]

    def rec(S, fs, lst, hst):
        if len(S) >= Lmax:
            return
        amax = (S[-1][0] + 1) if S else 0
        for a in range(amax + 1):
            for b in range(a + 1):
                for c in range(min(b, 1) + 1):
                    P = S + ((a, b, c),)
                    fp = fs + [a, b, c]
                    l2 = lo_state(fp, flo)
                    if l2 < 0:
                        continue
                    h2 = hi_state(fp, fhi)
                    if h2 < 0:
                        continue
                    try:
                        Q = tuple(f(list(P)))
                    except Exception:
                        Q = None
                    if Q is not None and len(Q) == LT and isstd(P, 'BMS'):
                        d = sum(1 for x, y in zip(Q, T) if tuple(x) != tuple(y))
                        if d <= maxdiff:
                            out.append((d, P, Q))
                    if Q is not None:
                        if len(Q) > LT + SL:
                            continue
                        if lcp(Q, T) < len(Q) - SL:
                            continue
                    if not isstd(P, 'BMS'):
                        continue
                    cnt[0] += 1
                    if cnt[0] >= nodecap:
                        hitcap[0] = True
                        return
                    rec(P, fp, l2, h2)
                    if hitcap[0]:
                        return

    rec((), [], lo_state([], flo), hi_state([], fhi))
    out.sort(key=lambda t: (t[0], len(t[1])))
    seen, res = set(), []
    for d, P, Q in out:
        if P in seen:
            continue
        seen.add(P); res.append((d, P, Q))
        if len(res) >= topk:
            break
    return T, res, ('cap' if hitcap[0] else 'ok', cnt[0])


if __name__ == '__main__':
    from core import parse
    import time
    AS = {'A1': '(0,0,0)(1,1,1)(2,0,0)(3,1,1)(1,1,1)',
          'A2': '(0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,1,0)'}
    for nm, s in AS.items():
        A = parse(s, 3)
        for m in (1, 2, 3):
            t0 = time.time()
            T, res, st = nearmiss(A, m, SL=int(sys.argv[1]) if len(sys.argv)>1 else 6,
                                  nodecap=int(sys.argv[2]) if len(sys.argv)>2 else 60000)
            print('%s m=%d  T=%s  %s 節点 %d  %.0fs'
                  % (nm, m, show([list(c) for c in T]), st[0], st[1], time.time()-t0))
            for d, P, Q in res[:4]:
                print('    差 %d  B=%s' % (d, show([list(c) for c in P])))
                print('           f(B)=%s' % show([list(c) for c in Q]))
            sys.stdout.flush()
