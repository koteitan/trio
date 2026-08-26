"""シートの BMS 列の打ち間違いを探す。

ある行の BMS を 1〜2 手で編集して、次の 4 条件をすべて満たすものを探す:
  (1) 編集後が BMS 標準形
  (2) 他の行の BMS と重複しない
  (3) その行を編集後の BMS ＋ シートの DBMS で置き換えても順序同型が壊れない
  (4) 変換器の出力がシートの DBMS と一致する

使い方: python3 typo_search.py 1192 1532
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_sheet import load
from core import isstd, show, cmpmat
from order_check import check
import rule as R


def edits1(m, Y=3):
    """1 手の編集: 1 成分を変える / 1 列消す / 1 列入れる"""
    n = len(m)
    for i in range(n):
        for y in range(Y):
            for v in range(0, 9):
                if v == m[i][y]:
                    continue
                c = list(m[i]); c[y] = v
                yield m[:i] + (tuple(c),) + m[i + 1:]
    for i in range(1, n):
        yield m[:i] + m[i + 1:]
    cols = sorted(set(m) | {(a, b, c) for a in range(9) for b in range(a + 1)
                            for c in range(b + 1)})
    for i in range(1, n + 1):
        for c in cols:
            yield m[:i] + (c,) + m[i:]


def search(row, twostep=False):
    d = [x for x in load() if x[3] == 3]
    tgt = [x for x in d if x[0]['row'] == row]
    if not tgt:
        print('row %s は Y=3 にない' % row); return
    r, mb, md, _ = tgt[0]
    others = [(x[0]['row'], x[1], x[2]) for x in d if x[0]['row'] != row]
    ok = [(rw, b, R.convert(b, 3)) for rw, b, dd in others if R.convert(b, 3) == dd]
    seen = {b for rw, b, dd in others}
    base = len(check(ok))
    print('row %s  基準違反 %d  bms %s' % (row, base, show(mb, 1)))
    print('        シート dbms %s' % show(md, 1))
    found = []
    gen = edits1(mb)
    if twostep:
        gen = itertools.chain(gen, (m2 for m1 in edits1(mb) if isstd(m1, 'BMS')
                                    for m2 in edits1(m1)))
    for cand in gen:
        if cand in seen or cand == mb:
            continue
        if not isstd(cand, 'BMS'):
            continue
        try:
            g = R.convert(cand, 3)
        except Exception:
            continue
        if g != md:
            continue
        v = check(ok + [(row, cand, md)])
        if len(v) > base:
            continue
        found.append(cand)
        print('   ○ %s' % show(cand, 1))
    if not found:
        print('   （見つからず）')
    return found


if __name__ == '__main__':
    for a in sys.argv[1:]:
        search(int(a))
