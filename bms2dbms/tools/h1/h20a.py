# -*- coding: utf-8 -*-
"""H20 (1): 残る 7 件の逆転で、**どの条件が真から偽に落ちるか**。"""
import sys
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import rows3, provc, core, r7
from rows3 import (is_branch, is_w_col, copy_head, par0, closes_unit,
                   closes_top, p0_shallow, aw_flip, hi_block2, term_top)
from core import show

P = r7.stts_pool(5, 10)
IM = []
for i, M in enumerate(P):
    if i % 20000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    IM.append(tuple(tuple(c) for c in rows3.b2d3(list(M))))
o = sorted(range(len(P)), key=lambda i: P[i])
seq = [IM[i] for i in o]
bad = [i for i in range(len(seq) - 1) if seq[i] >= seq[i + 1]]
print('残る逆転 %d 件' % len(bad))
c = Counter()
for i in bad:
    M1, M2 = P[o[i]], P[o[i + 1]]
    C1, PR1 = provc.b2d3p(list(M1))
    C2, PR2 = provc.b2d3p(list(M2))
    k = 0
    while k < min(len(C1), len(C2)) and C1[k] == C2[k]:
        k += 1
    w1 = PR1[k] if k < len(PR1) else None
    w2 = PR2[k] if k < len(PR2) else None
    off = w1[1] if w1 else None
    print()
    print('  M1 = %s' % show([list(x) for x in M1]))
    print('  M2 = %s' % show([list(x) for x in M2]))
    print('  ずれ k=%d  fM1[k]=%s  fM2[k]=%s' % (k, C1[k] if k < len(C1) else None,
                                                 C2[k] if k < len(C2) else None))
    print('  M1: %s   M2: %s' % (w1, w2))
    if off is not None and off < len(M1) and off < len(M2):
        p = M1[off]
        for nm, f in (('closes_unit(nxt)',
                       lambda Mo: closes_unit(Mo[off + 1] if off + 1 < len(Mo) else None)),
                      ('closes_top',
                       lambda Mo: closes_top(Mo, off,
                                             Mo[off + 1] if off + 1 < len(Mo) else None)),
                      ('p0_shallow', lambda Mo: p0_shallow(Mo, off)),
                      ('aw_flip', lambda Mo: aw_flip(Mo, off)),
                      ('hi_block2', lambda Mo: hi_block2(Mo, off)),
                      ('last_w', lambda Mo: is_w_col(Mo[-1])),
                      ('chead_after0',
                       lambda Mo: not any(copy_head(Mo, t)
                                          for t in range(off + 1, len(Mo))))):
            try:
                a, b = f(M1), f(M2)
            except Exception:
                continue
            if a != b:
                print('     **%s: M1=%s -> M2=%s**%s'
                      % (nm, a, b, '  ← 真から偽に落ちる' if (a and not b) else ''))
                c[(nm, a, b)] += 1
print()
print('落ちた条件の集計:')
for kk, v in c.most_common():
    print('   %-24s %s -> %s   %d' % (kk[0], kk[1], kk[2], v))
