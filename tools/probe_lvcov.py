# -*- coding: utf-8 -*-
"""深さの梯子 `Lv d`（Small.lean）を足すと、緑の補題の閉包はどこまで伸びるか。

`probe_bumpcov.py` の規則 R0-R6/R8/R8g/R9/R10 に、今回証明した 2 本を足す。
どちらも Lean の定理に 1 対 1 で対応する（神託ではない）。

  R11 Lv_snoc : Lv d A → A ++ [(d,1,0)] ∈ W 0
  R12 Lv_hang : Lv d A → Bok B → A ++ B↑d ∈ W 0        （d=1 は bump と同じ）

`Lv d A` は判定不能なので**下界**を取る（見つかれば健全）:
  1 ∈ lvset(A)                         Aok A
  d+1 ∈ lvset(A)   if A = A0 ++ [(d,1,0)] かつ d ∈ lvset(A0)      （Lv_Dg の段）
  2 ∈ lvset(A)     if A = A0 ++ Mseq m かつ Aok A0                （mseq_mem）
"""
import os, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import probe_bumpcov as P
from probe_bumpcov import s, lev, srow, forms, deep, deep_d, gen_ok, unbump, CAP
from trio import parent


def aok(A, known):
    return (len(A) > 0 and A in known and deep(A) and gen_ok(A))


def mseq_split(A):
    """A = A0 ++ (1,1,0)(2,1,0)^m の A0（無ければ None）。"""
    i = len(A) - 1
    while i >= 0 and A[i] == (2, 1, 0):
        i -= 1
    if i < 0 or A[i] != (1, 1, 0):
        return None
    return A[:i]


def lvset(A, known, memo):
    """Lv d A が確実に言える d の集合（下界）。"""
    if A in memo:
        return memo[A]
    memo[A] = set()                       # 再入よけ
    out = set()
    if aok(A, known):
        out.add(1)
        if len(A) >= 2:
            c = A[-1]
            if c[2] == 0 and c[1] == 1 and c[0] >= 1:
                if c[0] in lvset(A[:-1], known, memo):
                    out.add(c[0] + 1)
        a0 = mseq_split(A)
        if a0 is not None and aok(a0, known):
            out.add(2)
    memo[A] = out
    return out


def shape_shift(C):
    """C = B↑d となる (d, B)。d は C の最小深さ。C が空なら None。"""
    if not C:
        return None
    d = min(c[0] for c in C)
    if d < 1:
        return None
    return d, tuple((c[0] - d, c[1], c[2]) for c in C)


def rule_lv(M, known, memo):
    if len(M) < 2:
        return None
    # R11
    c = M[-1]
    if c[1] == 1 and c[2] == 0 and c[0] >= 1:
        if c[0] in lvset(M[:-1], known, memo):
            return 'R11'
    # R12
    for i in range(1, len(M)):
        A, C = M[:i], M[i:]
        r = shape_shift(C)
        if r is None:
            continue
        d, B = r
        if d in lvset(A, known, memo) and gen_ok(B) and B in known:
            return 'R12' if d >= 2 else 'R12(d=1)'
    return None


K = 5
CAPN = 40


def rule_n(M, known):
    """節2 ＋ n の帰納法の代用（n<=K で打ち切るので規則としては不健全。
    「手で n の帰納法を書けば届く」範囲の目安を測るためだけに使う）。"""
    if len(M) < 2:
        return None
    from trio import expand
    for n in range(1, K + 1):
        E = tuple(expand(list(M), n))
        if len(E) > CAPN or E not in known:
            return None
    return 'Rn'


def closure(D, use_lv, use_n=False):
    known, tag = set(), {}
    for _ in range(80):
        added = 0
        memo = {}
        for M in sorted(D, key=len):
            if M in known:
                continue
            r = P.rule(M, known, True)
            if r is None and use_lv:
                r = rule_lv(M, known, memo)
            if r is None and use_n:
                r = rule_n(M, known)
            if r:
                known.add(M); tag[M] = r; added += 1
        if not added:
            break
    return tag


if __name__ == '__main__':
    LEN = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    VAL = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    F = forms(LEN, VAL)
    print('z<2 標準形（<=%d 列・値<=%d）: %d 個' % (LEN, VAL, len(F)))
    D = set(F)
    front = list(F)
    for _ in range(8):
        nxt = []
        for M in front:
            for d in P.deps(M):
                if d not in D:
                    D.add(d); nxt.append(d)
        front = nxt
        if not front:
            break
    print('母集団: %d 個' % len(D))
    for use_lv, use_n, label in (
            (False, False, '梯子なし（R0-R10）'),
            (True, False, '梯子あり（＋R11/R12）'),
            (True, True, '梯子＋n の帰納法の目安（Rn）')):
        P.ORACLE_PC = False
        P.ORACLE_GEN = True
        P.ORACLE_TOW1 = 'tow1'
        tag = closure(D, use_lv, use_n)
        got = [M for M in F if M in tag]
        print('%-28s 標準形 %4d / %4d   %s'
              % (label, len(got), len(F), dict(Counter(tag[M] for M in got))))
        if use_n:
            rest = sorted((M for M in F if M not in tag), key=lambda M: (len(M), M))
            print('  届かない最小のもの:')
            for M in rest[:10]:
                print('   ', s(M))
