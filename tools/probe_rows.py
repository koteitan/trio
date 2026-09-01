# -*- coding: utf-8 -*-
"""シートの行を順に、証明済みの規則の閉包で届くかどうか判定する。

規則は probe_bumpcov.py と同じ（R0-R6 ＋ R8 bump ＋ R8g bump 一般版 ＋ R9 snoc_row1）。
すべて Lean で緑。神託（PrefixCopies）は入れない。
"""
import csv, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import probe_bumpcov as P

P.ORACLE_PC = False
P.ORACLE_GEN = True
P.ORACLE_TOW1 = True


def parse(s):
    out = []
    for t in s.strip().strip(')').split(')('):
        out.append(tuple(int(x) for x in t.strip('()').split(',')))
    return tuple(out)


def reach(M, depth=6):
    D, front = {M}, [M]
    for _ in range(depth):
        nxt = []
        for X in front:
            for d in P.deps(X):
                if d not in D:
                    D.add(d); nxt.append(d)
        front = nxt
        if not front or len(D) > 20000:
            break
    tag = P.closure(D, True)
    return tag.get(M)


if __name__ == '__main__':
    lo = int(sys.argv[1]); hi = int(sys.argv[2])
    rows = list(csv.reader(open('tmp/fixed-sheet/to-psi-I.tsv'), delimiter='\t'))
    n_ok = 0; n = 0
    for r in rows[1:]:
        if not r[0].isdigit(): continue
        k = int(r[0])
        if not (lo <= k <= hi): continue
        m = r[1].replace(' ', '')
        if not m.startswith('('): continue
        M = parse(m)
        t = reach(M)
        n += 1; n_ok += (t is not None)
        print('%-5s %-4s %-52s %s' % (r[0], t or '✗', m, r[3]))
    print('--- %d / %d' % (n_ok, n))
