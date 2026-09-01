# -*- coding: utf-8 -*-
"""行293 の還元閉包で「行 1 リフト」が起きる箇所を拾い、2 つのマスクを比べる。

RESIDUE-PROBLEM.md §4.9:
  BM4 が実際に施すリフトのマスク  = バッドルート j0 の**添字**の子孫錐（le1）
  証明済みリフト法則のマスク       = 行 1 の**値**の上方集合
2 つが一致すれば (WL) は既証の法則から無料。差はちょうど「行 1 のタイ」で出る。
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import expand

def s(m): return ''.join('(%d,%d,%d)' % tuple(c) for c in m) or '(空)'
def e0(M, j): return M[j][0]
def e1(M, j): return M[j][1]
def e2(M, j): return M[j][2]
def srow(c): return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)

def nextrel0(M, a, b):
    return (a < b and e0(M, a) < e0(M, b)
            and all(e0(M, b) <= e0(M, j) for j in range(a + 1, b)))

def le0set(M, a):
    """a から le0 で到達できる添字の集合。"""
    out = {a}; front = [a]
    while front:
        nxt = []
        for x in front:
            for y in range(x + 1, len(M)):
                if y not in out and nextrel0(M, x, y):
                    out.add(y); nxt.append(y)
        front = nxt
    return out

def le0(M, a, b):
    return b in le0set(M, a)

def nextrel1(M, a, b):
    if not (a < b and e1(M, a) < e1(M, b) and le0(M, a, b)):
        return False
    for j in range(a + 1, len(M)):
        if le0(M, j, b) and e1(M, b) > e1(M, j):
            return False
    return True

def le1set(M, a):
    out = {a}; front = [a]
    while front:
        nxt = []
        for x in front:
            for y in range(x + 1, len(M)):
                if y not in out and nextrel1(M, x, y):
                    out.add(y); nxt.append(y)
        front = nxt
    return out

def parent_i(M, i, j1):
    """行 i の親（無ければ None）。"""
    if i == 0:
        cand = [a for a in range(j1) if nextrel0(M, a, j1)]
    elif i == 1:
        cand = [a for a in range(j1) if nextrel1(M, a, j1)]
    else:
        L1 = None
        cand = []
        for a in range(j1):
            if not (e2(M, a) < e2(M, j1)): continue
            if a not in le1set(M, a): pass
            if j1 not in le1set(M, a): continue
            ok = True
            for j in range(a + 1, len(M)):
                if j1 in le1set(M, j) and e2(M, j1) > e2(M, j):
                    ok = False; break
            if ok: cand.append(a)
    return cand[-1] if cand else None

def closure(seeds, K=4, cap=26, maxsize=4000):
    seen = set(); front = [tuple(m) for m in seeds]
    while front and len(seen) < maxsize:
        nxt = []
        for M in front:
            if M in seen or len(M) == 0: continue
            seen.add(M)
            for n in range(1, K + 1):
                E = tuple(tuple(c) for c in expand(list(M), n))
                if len(E) <= cap and E not in seen:
                    nxt.append(E)
        front = nxt
    return seen

if __name__ == '__main__':
    R293 = [(0,0,0),(1,1,1),(1,1,0),(2,2,0),(3,2,0)]
    C = closure([R293])
    print('行293 の還元閉包: %d 個（<=26 列, n<=4）' % len(C))
    lifts = 0; ties = 0; mism = 0; ex = []
    for M in C:
        L = list(M); x = len(L) - 1
        if x < 1: continue
        t = srow(L[x])
        if t != 2: continue                 # 行 1 リフトが乗るのは srow = 2 のときだけ
        j0 = parent_i(L, 2, x)
        if j0 is None: continue
        lifts += 1
        blk = range(j0, x)
        idx = le1set(L, j0)                 # 添字マスク
        val = {j for j in blk if e1(L, j0) <= e1(L, j)}   # 値マスク
        idxb = {j for j in blk if j in idx}
        tie = {j for j in blk if e1(L, j) == e1(L, j0) and j != j0}
        if tie: ties += 1
        if idxb != val:
            mism += 1
            if len(ex) < 5:
                ex.append((s(L), j0, sorted(idxb), sorted(val), sorted(tie)))
    print('  srow=2 で親ありの箇所（＝行 1 リフトが乗る）: %d' % lifts)
    print('  行 1 のタイがある箇所                      : %d' % ties)
    print('  添字マスク ≠ 値マスク                      : %d' % mism)
    for e in ex:
        print('   ex %s  j0=%d  添字%s  値%s  タイ%s' % e)

def scan(name, seeds, K=4, cap=26, maxsize=4000, verbose=True):
    C = closure(seeds, K, cap, maxsize)
    lifts = ties = mism = 0; ex = []
    for M in C:
        L = list(M); x = len(L) - 1
        if x < 1: continue
        if srow(L[x]) != 2: continue
        j0 = parent_i(L, 2, x)
        if j0 is None: continue
        lifts += 1
        blk = range(j0, x)
        idx = le1set(L, j0)
        val = {j for j in blk if e1(L, j0) <= e1(L, j)}
        idxb = {j for j in blk if j in idx}
        tie = {j for j in blk if e1(L, j) == e1(L, j0) and j != j0}
        if tie: ties += 1
        if idxb != val:
            mism += 1
            if len(ex) < 3: ex.append((s(L), j0, sorted(idxb), sorted(val), sorted(tie)))
    if verbose:
        print('%-34s 閉包 %5d  リフト %5d  タイ %4d  不一致 %4d'
              % (name, len(C), lifts, ties, mism))
        for e in ex:
            print('     ex %s j0=%d 添字%s 値%s タイ%s' % e)
    return lifts, ties, mism
