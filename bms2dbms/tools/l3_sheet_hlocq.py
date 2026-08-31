# -*- coding: utf-8 -*-
"""L3 §250.2: BM4-Analysis シート（psiI.json の DBMS 列）で hlocQ の窓遺伝を測る。

  python3 bms2dbms/tools/l3_sheet_hlocq.py

分母 = srow >= 1 かつ最終列の親が一意かつ窓の長さ >= 2 の窓。
分子 = 窓で hlocQ が破れるもの。あわせて hlocQ(B) 自身の成否も出す。
"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import parse


def e(M, i, j):
    return M[j][i] if j < len(M) else 0


def nextrel0(M, a, b):
    if not (a < b < len(M)):
        return False
    if not e(M, 0, a) < e(M, 0, b):
        return False
    return all(e(M, 0, b) <= e(M, 0, q) for q in range(a + 1, b))


def _closure(M, a, step):
    R = {a}
    ch = True
    while ch:
        ch = False
        for x in list(R):
            for y in range(x + 1, len(M)):
                if y not in R and step(M, x, y):
                    R.add(y)
                    ch = True
    return R


def le0(M, a, b):
    return a < len(M) and b < len(M) and b in _closure(M, a, nextrel0)


def nextrel1(M, a, b):
    if not (a < b < len(M)):
        return False
    if not e(M, 1, a) < e(M, 1, b):
        return False
    if not le0(M, a, b):
        return False
    return all(e(M, 1, b) <= e(M, 1, q)
               for q in range(a + 1, b + 1) if le0(M, q, b))


def le1(M, a, b):
    return a < len(M) and b < len(M) and b in _closure(M, a, nextrel1)


def srow(M, j):
    return 2 if e(M, 2, j) > 0 else (1 if e(M, 1, j) > 0 else 0)


def parents(M, i, j):
    if i == 0:
        return [y for y in range(j) if nextrel0(M, y, j)]
    if i == 1:
        return [y for y in range(j) if nextrel1(M, y, j)]
    return [y for y in range(j)
            if e(M, 2, y) < e(M, 2, j) and le1(M, y, j)
            and all(e(M, 2, j) <= e(M, 2, q)
                    for q in range(y + 1, j + 1) if le1(M, q, j))]


def hlocQ(M):
    for j in range(1, len(M)):
        if e(M, 2, j) > 0:
            if not parents(M, 2, j):
                return False
        elif e(M, 1, j) > 0 and not any(
                le0(M, y, j) and e(M, 1, y) < e(M, 1, j) for y in range(j)):
            return False
    return True


def main():
    data = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'psiI.json')
    seen, mats = set(), []
    for r in json.load(open(data)):
        s = r.get('dbms')
        if not s or 'Empty' in s:
            continue
        try:
            M = parse(s)
        except Exception:
            continue
        if not M:
            continue
        cols = tuple(tuple(list(c) + [0, 0, 0])[:3] for c in M)
        if cols not in seen:
            seen.add(cols)
            mats.append(list(cols))
    den = brk = brkH = 0
    srcs, shortest = set(), None
    for M in mats:
        if len(M) > 26 or any(c[2] > 1 for c in M):
            continue
        for j in range(2, len(M)):
            B = M[:j + 1]
            s = srow(B, j)
            if s == 0:
                continue
            ps = parents(B, s, j)
            if len(ps) != 1:
                continue
            p = ps[0]
            if j - p < 2:
                continue
            den += 1
            V = B[p:j]
            if not hlocQ(V):
                brk += 1
                srcs.add(tuple(map(tuple, M)))
                if hlocQ(B):
                    brkH += 1
                if shortest is None or len(B) < len(shortest[0]):
                    shortest = (B, p, V)
    print(f'distinct sheet matrices : {len(mats)}')
    print(f'windows tested (denom)  : {den}')
    print(f'hlocQ breaks            : {brk} ({100 * brk / den:.4f}%)')
    print(f'  of which hlocQ(B) too : {brkH}')
    print(f'source matrices w/ break: {len(srcs)}')
    print(f'shortest example        : {shortest}')
    orph(mats)


def orph(mats):
    '''窓で孤児になった列の親が、B のどこにいるかを数える。'''
    import collections
    cnt, ex, den = collections.Counter(), {}, 0
    for M in mats:
        if len(M) > 26 or any(c[2] > 1 for c in M):
            continue
        for j in range(2, len(M)):
            B = M[:j + 1]
            s = srow(B, j)
            if s == 0:
                continue
            ps = parents(B, s, j)
            if len(ps) != 1:
                continue
            p = ps[0]
            if j - p < 2:
                continue
            V = B[p:j]
            for t in range(1, len(V)):
                if e(V, 2, t) > 0:
                    ok = bool(parents(V, 2, t))
                else:
                    ok = e(V, 1, t) == 0 or any(
                        le0(V, y, t) and e(V, 1, y) < e(V, 1, t)
                        for y in range(t))
                if ok:
                    continue
                den += 1
                a = p + t
                pb = parents(B, srow(B, a), a)
                if not pb:
                    k = 'orphan in B (snoc_orphan_W applies)'
                elif all(y < p for y in pb):
                    k = 'parent strictly before p (OrphOK)'
                else:
                    k = 'parent >= p'
                cnt[k] += 1
                ex.setdefault(k, (B, p, t, pb))
    print()
    print(f'breaking columns (denom): {den}')
    for k, v in cnt.items():
        print(f'  {k}: {v} ({100 * v / den:.4f}%)')
    for k, v in ex.items():
        print(f'  ex {k}: {v}')


if __name__ == '__main__':
    main()
