"""標準形の右端の道の各節点でブロックの主張を検査し、到達するパラメタを集める。"""
import sys, collections
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import core
from core import expand, show, pim
from rows2 import gen, convC, split


def check(B, d, plev, first, force, nmax=3, mmax=14, dn=5):
    out = tuple(convC(list(B), d, plev, first, force))
    for n in range(1, nmax + 1):
        ok = False
        for np_ in range(n, n + dn + 1):
            tgt = tuple(convC(list(expand(tuple(B), np_)), d, plev, first, force))
            for m in range(1, mmax + 1):
                if tuple(expand(out, m)) == tgt:
                    ok = True
                    break
            if ok:
                break
        if not ok:
            return n
    return None


def walk(M, d, plev, first, force, out):
    if not M:
        return
    p, r = M[0], M[1:]
    s = p[1]
    A, T = split(p, r)
    out.append((tuple(M), d, plev, first, force))
    lad = first and s == plev + 1 and (d <= s or force)
    dd = d + 1 if lad else (s + 1 if (s > 0 and d <= s) else d)
    if T:
        walk(list(T), d, s, False, False, out)
    elif A:
        walk(list(A), dd + 1, s, True, (not lad) and first and s == plev, out)


def main(lim=8, docheck=1):
    Ms = gen('BMS', lim)
    nodes = set()
    for i, M in enumerate(Ms):
        if i % 20000 == 0:
            core._exp_memo.clear(); core._flat_memo.clear()
        acc = []
        walk(list(M), 0, 0, True, False, acc)
        nodes.update(acc)
    print('標準形 <=%d 列: %d、右端の道の節点（重複除去）: %d' % (lim, len(Ms), len(nodes)))
    if docheck:
        bad = []
        for k, (B, d, plev, first, force) in enumerate(sorted(nodes)):
            if k % 20000 == 0:
                core._exp_memo.clear(); core._flat_memo.clear()
            if len(B) < 2:
                continue
            r = check(B, d, plev, first, force)
            if r is not None:
                bad.append((B, d, plev, first, force, r))
        print('ブロックの主張が破れる節点:', len(bad))
        for x in bad[:10]:
            print('   ', show(x[0]), x[1:])
    import pickle
    with open('/tmp/nodes.pkl', 'wb') as f:
        pickle.dump(nodes, f)


if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    main(*a) if a else main()
