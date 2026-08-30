# -*- coding: utf-8 -*-
"""**H43-b の詰め ＋ H43-c —— 復活したとき、塔の形はどう変わるか。**"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import r66, trio, h41, h42, h43b
import wcert as wc
from collections import Counter

rows = h43b.rows if hasattr(h43b, 'rows') else None
T = r66.load_ladder()
rows = []
for row, M, ocf in T:
    f = h43b.feats(M)
    if f is None:
        continue
    rows.append((row, M, ocf, h41.classify(M, 6)[0], f,
                 f['loc'] != '段 1（新しい段）'))

print('**★ 判別子: 「段の最後の列の行 1 が上がるか」（`b >= 2` に限る）**')
R2 = [r for r in rows if r[4]['b'] >= 2]
cc = Counter()
for row, M, ocf, kd, f, esc in R2:
    cc[(f['lastmask'], esc)] += 1
for k in (0, 1):
    e, s = cc[(k, True)], cc[(k, False)]
    print('   印=%d（%s） 逃げる **%5d / %5d (%.1f%%)**'
          % (k, '上がらない' if k == 0 else '上がる', e, e + s,
             100.0 * e / max(1, e + s)))
print()
print('   種別ごと（`b >= 2`）:')
for kd in ('a', 'b'):
    cc2 = Counter()
    for row, M, ocf, k2, f, esc in R2:
        if k2 != kd:
            continue
        cc2[(f['lastmask'], esc)] += 1
    for k in (0, 1):
        e, s = cc2[(k, True)], cc2[(k, False)]
        if e + s:
            print('      (%s) 印=%d  逃げる %5d / %5d (%.1f%%)'
                  % (kd, k, e, e + s, 100.0 * e / (e + s)))
print()
ex = [r for r in R2 if r[4]['lastmask'] == 0 and not r[5]]
print('   **例外（印=0 なのに逃げない）%d 件。最小のもの:**' % len(ex))
for row, M, ocf, kd, f, esc in sorted(ex, key=lambda r: r[0])[:4]:
    print('      行 %-5d %s  種別=%s b=%d t=%d 印=%s'
          % (row, ocf, kd, f['b'], f['t'], f['mask']))
print()

print('**H43-c 復活したときの展開の形 —— `A` が伸びるだけか、`Q` も変わるか**')
esc = [r for r in rows if r[5] and r[4]['b'] >= 2]
print('   `b>=2` で逃げる %d 件について、`M⟦2⟧` を測り直す' % len(esc))
c = Counter()
for row, M, ocf, kd, f, e in esc:
    T2 = [tuple(c2) for c2 in trio.expand(list(M), 2)]
    k2, A2, Q2, e2, d2 = h41.classify(T2, 6)
    lay1 = h42.layout(M, 6)
    lay2 = h42.layout(T2, 6)
    if k2 in ('c', 'd', '?') or lay2 is None or lay1 is None:
        c[('**塔でなくなる**', k2)] += 1
        continue
    a1, b1, E1 = lay1
    a2, b2, E2 = lay2
    A1_ = tuple(E1[1][:a1])
    A2_ = tuple(E2[1][:a2])
    Q1_ = tuple(E1[1][a1:a1 + b1])
    Q2_ = tuple(E2[1][a2:a2 + b2])
    same_q = (Q1_ == Q2_)
    ext_a = (A2_[:len(A1_)] == A1_)
    c[('塔のまま（種別 %s）' % k2,
       ('**Q は同じ**' if same_q else 'Q も変わる'),
       ('A は伸びるだけ' if ext_a else 'A も書き換わる'))] += 1
for k, v in sorted(c.items(), key=lambda t: -t[1]):
    print('   %-58s %5d (%.1f%%)' % (str(k), v, 100.0 * v / max(1, len(esc))))
print()
print('   段の幅の変化 `b` -> `b2`:')
cb = Counter()
for row, M, ocf, kd, f, e in esc:
    T2 = [tuple(c2) for c2 in trio.expand(list(M), 2)]
    l1, l2 = h42.layout(M, 6), h42.layout(T2, 6)
    if l1 and l2:
        cb[('同じ' if l1[1] == l2[1] else
            ('%+d' % (l2[1] - l1[1])))] += 1
for k, v in cb.most_common(6):
    print('      %-8s %5d' % (k, v))
print()
print('**退化検査**')
f_ = lambda r: r[5]
wc.audit(R2, f_, lambda r: r[4]['lastmask'] == 0,
         '「逃げる」 vs 「段の最後の列の印 = 0」（b>=2）')
wc.audit(R2, f_, lambda r: r[4]['t'] == 2, '「逃げる」 vs 「t = 2」（b>=2）')
