# -*- coding: utf-8 -*-
"""**H43-a —— `A` 側の覆いを `ladder.Cert` で測り直す。**

H41 §69 / H42 §4 の「`wcert(A)` が 41% で頭打ち」は `wcert` が節 2（展開）を
使っていないため（リード §42）。`ladder.Cert` は節 2 を再帰的に回す。

`A` の取り方は 2 通りあるので両方出す:
    `A_0` = 私の切り方（段 0 を含まない固定接頭辞）
    `A_1` = `ladder.family` の切り方 = `M⟦1⟧`（段 0 を含む）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import r66, ladder, h42, trio
from wcert import wcert
from collections import Counter

T = r66.load_ladder()
print('母集団: `psiI.json` の 3 行 z<2 **%d 行**（シート行番号順）' % len(T))
print()

rows = []
for row, M, ocf in T:
    lay = h42.layout(M, 6)
    if lay is None:
        continue
    a, b, E = lay
    w = h42.where(M, 4)
    esc = any('逃げる' in x[0] for x in w)
    A0 = tuple(E[1][:a])
    A1 = tuple(E[1])
    rows.append((row, M, ocf, a, b, A0, A1, esc))
print('塔になる行 %d（`b` の内訳: %s）'
      % (len(rows), dict(Counter(min(r[4], 5) for r in rows))))
print()

MODES = (('strict（Lean 証明ずみのみ）', (), False),
         ('+TOW', ('TOW',), False),
         ('+LTOW', ('TOW', 'LTOW'), False),
         ('+MTOW', ('TOW', 'LTOW', 'MTOW'), False),
         ('**+MLIFT**', ('TOW', 'LTOW', 'MTOW'), True))

print('**A 側の覆い（`ladder.Cert`）**')
print('| 仮定 | `Cert(A_0)` | `Cert(A_1)=Cert(M⟦1⟧)` | `Cert(M)` |')
print('|---|--:|--:|--:|')
res = {}
for name, asm, ml in MODES:
    ladder.MLIFT = ml
    C = ladder.Cert(asm)
    t0 = time.time()
    n0 = sum(1 for r in rows if C(r[5], 80))
    n1 = sum(1 for r in rows if C(r[6], 80))
    nm = sum(1 for r in rows if C(r[1], 80))
    res[name] = (n0, n1, nm)
    print('| %s | %d (%.1f%%) | %d (%.1f%%) | %d (%.1f%%) |'
          % (name, n0, 100.0 * n0 / len(rows), n1, 100.0 * n1 / len(rows),
             nm, 100.0 * nm / len(rows)))
ladder.MLIFT = False
w0 = sum(1 for r in rows if wcert(list(r[5])))
print('| （参考）`wcert(A_0)` 単独 | %d (%.1f%%) | | |'
      % (w0, 100.0 * w0 / len(rows)))
print()

print('**★ (TOWER-易) の値打ち = 「逃げない ＋ `A` が覆える」**')
safe = [r for r in rows if not r[7]]
safe2 = [r for r in safe if r[4] >= 2]
all2 = [r for r in rows if r[4] >= 2]
print('| 仮定 | 逃げない かつ `Cert(A_0)`（全体 %d 行）| 同（`b>=2` %d 行）|'
      % (len(rows), len(all2)))
print('|---|--:|--:|')
for name, asm, ml in MODES:
    ladder.MLIFT = ml
    C = ladder.Cert(asm)
    x = sum(1 for r in safe if C(r[5], 80))
    y = sum(1 for r in safe2 if C(r[5], 80))
    print('| %s | %d (%.1f%%) | %d (%.1f%%) |'
          % (name, x, 100.0 * x / len(rows), y, 100.0 * y / len(all2)))
ladder.MLIFT = False
print()
print('   （逃げない行は 全体 %d (%.1f%%)、`b>=2` %d (%.1f%%)）'
      % (len(safe), 100.0 * len(safe) / len(rows),
         len(safe2), 100.0 * len(safe2) / len(all2)))
print()
print('**退化検査**')
import wcert as wc
ladder.MLIFT = True
C = ladder.Cert(('TOW', 'LTOW', 'MTOW'))
f = lambda r: C(r[5], 80) is not None
for nm2, tv in (('「|A_0| <= 1」', lambda r: len(r[5]) <= 1),
                ('「A_0 の行 2 が全部 0」',
                 lambda r: all(q[2] == 0 for q in r[5])),
                ('「逃げない」', lambda r: not r[7])):
    wc.audit(rows, f, tv, '`Cert(A_0)` vs ' + nm2)
ladder.MLIFT = False
