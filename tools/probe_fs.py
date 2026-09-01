# -*- coding: utf-8 -*-
"""シートの各行について、**基本列 M[n] が届くか**を n=1..N で見る。

閉包（証明済みの規則）は「∀n の帰納法」を持たないので、`M` 自身が届かなくても
`M[n]` が全部届くなら「節 2 ＋ n の帰納法」で落ちる見込みが立つ。
"""
import csv, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import probe_bumpcov as P
from probe_rows import parse, reach
import trio

P.ORACLE_PC = False; P.ORACLE_GEN = True; P.ORACLE_TOW1 = True


def s(m): return ''.join('(%d,%d,%d)' % c for c in m)


if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    rows = list(csv.reader(open('tmp/fixed-sheet/to-psi-I.tsv'), delimiter='\t'))
    for r in rows[1:]:
        if not r[0].isdigit(): continue
        k = int(r[0])
        if not (lo <= k <= hi): continue
        m = r[1].replace(' ', '')
        if not m.startswith('('): continue
        M = parse(m)
        if reach(M) is not None:
            print('%-5s 済  %s' % (r[0], r[3])); continue
        tags = []
        for n in range(1, N + 1):
            E = tuple(trio.expand(list(M), n))
            tags.append(reach(E) or '✗')
        mark = '★ 基本列は全部届く' if all(t != '✗' for t in tags) else ' '.join(tags)
        print('%-5s %-42s %-34s %s' % (r[0], m, r[3], mark))
