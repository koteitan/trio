# -*- coding: utf-8 -*-
"""bump 帰納法の一般化（行 2 ≡ 0 ＋ Zroot）の 2 つの構造補題を全数検査する。

  (a) Zroot ∧ 行2≡0 は展開 `oper` で保たれる
  (b) Zroot ∧ 行2≡0 ∧ 根が (0,0,0) ∧ |B|>=2 ∧ 末尾列が非零
        ⟹ 末尾列は srow の行に親を持つ
  (c) 末尾列が非零・親あり ⟹ (A ++ bump B)[n] = A ++ bump(B[n])   （A は Deep）

Zroot B := 行 0 が 0 の列は必ず (0,0,0)。
"""
import sys, itertools
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def srow(M, j):
    return 2 if M[j][2] > 0 else (1 if M[j][1] > 0 else 0)


def zroot(M):
    return all(c[1] == 0 and c[2] == 0 for c in M if c[0] == 0)


def row2z(M):
    return all(c[2] == 0 for c in M)


def has_parent(M, j):
    return trio.parent(list(M), srow(M, j), j) is not None


def bump(M):
    return [(c[0] + 1, c[1], c[2]) for c in M]


def deep(M):
    return len(M) > 0 and M[0][0] == 0 and all(c[0] >= 1 for c in M[1:])


if __name__ == '__main__':
    V = int(sys.argv[1]) if len(sys.argv) > 1 else 3   # 値の上限
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 4   # 列数の上限
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 3   # 展開の n
    COLS = [(a, b, 0) for a in range(V + 1) for b in range(V + 1)]
    AS = [[(0, 0, 0), (1, 1, 1)], [(0, 0, 0), (1, 1, 1), (1, 0, 0)],
          [(0, 0, 0)], [(0, 0, 0), (1, 1, 0), (2, 2, 1)]]
    AS = [A for A in AS if deep(A)]
    tot = Counter()
    exa, exb, exc = [], [], []
    for ln in range(1, L + 1):
        for tail in itertools.product(COLS, repeat=ln - 1):
            B = [(0, 0, 0)] + list(tail)
            if not zroot(B):
                continue
            tot['B（Zroot・行2≡0・根 (0,0,0)）'] += 1
            # (a)
            for n in range(1, N + 1):
                E = trio.expand(list(B), n)
                if not (zroot(E) and row2z(E) and (not E or E[0] == (0, 0, 0))):
                    tot['**(a) 破れ**'] += 1
                    if len(exa) < 5: exa.append((B, n, E))
                    break
            else:
                tot['(a) OK'] += 1
            if len(B) < 2:
                continue
            # (b)
            j = len(B) - 1
            if B[j] != (0, 0, 0):
                if has_parent(B, j):
                    tot['(b) OK'] += 1
                else:
                    tot['**(b) 破れ**'] += 1
                    if len(exb) < 5: exb.append(B)
                    continue
                # (c)
                for A in AS:
                    for n in range(1, N + 1):
                        lhs = trio.expand(list(A) + bump(B), n)
                        rhs = list(A) + bump(trio.expand(list(B), n))
                        if lhs != rhs:
                            tot['**(c) 破れ**'] += 1
                            if len(exc) < 5: exc.append((A, B, n, lhs, rhs))
                            break
                    else:
                        continue
                    break
                else:
                    tot['(c) OK'] += 1
    print('値<=%d 列<=%d n<=%d' % (V, L, N))
    for k in sorted(tot):
        print('    %-40s %d' % (k, tot[k]))
    for e in exa: print('  a:', e)
    for e in exb: print('  b:', e)
    for e in exc: print('  c:', e)
