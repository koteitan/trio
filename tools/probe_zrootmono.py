# -*- coding: utf-8 -*-
"""一般 bump（Zroot ＋ Mono、行 2 も許す）の構造補題を全数検査する。

  (a) Zroot は展開で保たれる（行 2 ≡ 0 を仮定しない）
  (b) Mono（行2 <= 行1）は展開で保たれる
  (c) Zroot ∧ Mono ∧ 根が (0,0,0) ∧ |B|>=2 ∧ 末尾列が非零
        ⟹ 末尾列は srow の行に親を持つ
  (d) (A ++ bump B)[n] = A ++ bump(B[n])   （A は Deep）
"""
import sys, itertools
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/trio/tools')
import trio


def srow(M, j):
    return 2 if M[j][2] > 0 else (1 if M[j][1] > 0 else 0)


def zroot(M): return all(c[1] == 0 and c[2] == 0 for c in M if c[0] == 0)
def mono(M):  return all(c[2] <= c[1] for c in M)
def has_parent(M, j): return trio.parent(list(M), srow(M, j), j) is not None
def bump(M):  return [(c[0] + 1, c[1], c[2]) for c in M]
def deep(M):  return len(M) > 0 and M[0][0] == 0 and all(c[0] >= 1 for c in M[1:])


if __name__ == '__main__':
    V = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    N = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    COLS = [(a, b, c) for a in range(V + 1) for b in range(V + 1) for c in (0, 1)]
    AS = [[(0, 0, 0), (1, 1, 1)], [(0, 0, 0), (1, 1, 1), (1, 0, 0)],
          [(0, 0, 0)], [(0, 0, 0), (1, 1, 0), (2, 2, 1)], [(0, 0, 0), (2, 1, 1)]]
    AS = [A for A in AS if deep(A)]
    tot = Counter(); ex = {}
    for ln in range(1, L + 1):
        for tail in itertools.product(COLS, repeat=ln - 1):
            B = [(0, 0, 0)] + list(tail)
            if not (zroot(B) and mono(B)):
                continue
            tot['B（Zroot ∧ Mono ∧ 根 (0,0,0)）'] += 1
            for n in range(1, N + 1):
                E = trio.expand(list(B), n)
                if not zroot(E): tot['**(a) 破れ**'] += 1; ex.setdefault('a', (B, n, E)); break
                if not mono(E):  tot['**(b) 破れ**'] += 1; ex.setdefault('b', (B, n, E)); break
                if E and E[0] != (0, 0, 0):
                    tot['**根が動いた**'] += 1; ex.setdefault('r', (B, n, E)); break
            else:
                tot['(a)(b) OK'] += 1
            if len(B) < 2: continue
            j = len(B) - 1
            if B[j] == (0, 0, 0): continue
            if not has_parent(B, j):
                tot['**(c) 破れ**'] += 1; ex.setdefault('c', B); continue
            tot['(c) OK'] += 1
            bad = False
            for A in AS:
                for n in range(1, N + 1):
                    if trio.expand(list(A) + bump(B), n) != list(A) + bump(trio.expand(list(B), n)):
                        bad = True; ex.setdefault('d', (A, B, n)); break
                if bad: break
            tot['**(d) 破れ**' if bad else '(d) OK'] += 1
    print('値<=%d 列<=%d n<=%d' % (V, L, N))
    for k in sorted(tot): print('    %-40s %d' % (k, tot[k]))
    for k, v in ex.items(): print('  %s: %s' % (k, v))
