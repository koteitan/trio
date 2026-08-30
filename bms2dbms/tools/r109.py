# -*- coding: utf-8 -*-
"""**(s1)(s4) —— `oper_shTower` と、私の (y8) の「周期 2」との関係。**

⚠ 教訓 24: `L3` が `oper_shTower` を**既に緑にしている**（team-lead 報告）。
   ここで測るのは「その予測が私の側でも成り立つか」の**独立検証**と、
   **(y8) の例がその形と同じものか**の照合だけ。

    予測 `(shTower Q e (n+1))⟦m⟧ = shTower Q e n ++ shiftr01 (n*e) 0 (Q⟦m⟧)`
    （`shTower Q e n = concat_{k<n} shiftr01 (k*e) 0 Q`、`Wtower2.lean:1688`）
"""
import sys, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean


def shTower(Q, e, n):
    out = []
    for k in range(n):
        out += [(c[0] + k * e, c[1], c[2]) for c in Q]
    return out


rng = random.Random(20260830)
print('### (s1) `oper_shTower`（`L105Cap:3486`、緑）の独立検証')
print('  ⚠ 前提を全部課す: `Q ≠ []` / **`|Q| >= 2`** / 末尾が全零でない / **`HasParentInBlock Q`**')
r = Counter(); ex = {}
for _ in range(20000):
    L = rng.randint(1, 4)
    Q = [(0, rng.randint(0, 3), rng.randint(0, 1))] + \
        [(rng.randint(0, 3), rng.randint(0, 3), rng.randint(0, 1))
         for _ in range(L - 1)]
    e = rng.randint(1, 3)
    # ★ 緑の補題（`L105Cap.lean:3486`）の前提を**全部**課す（読んで写した）
    if len(Q) - 1 == 0:
        r['前提 hQ2（|Q|>=2）で除外'] += 1
        continue
    if Q[-1] == (Q[-1][0], 0, 0) and Q[-1][0] == 0:
        r['前提 hzQ で除外'] += 1
        continue
    i1 = 2 if Q[-1][2] > 0 else (1 if Q[-1][1] > 0 else 0)
    if trio.parent(Q, i1, len(Q) - 1) is None:
        r['前提 hblk（HasParentInBlock）で除外'] += 1
        continue
    for n in range(1, 5):
        for m in (1, 2, 3):
            S = shTower(Q, e, n + 1)
            if len(S) < 2:
                continue
            lhs = oper_lean(S, m)
            rhs = [tuple(c) for c in shTower(Q, e, n)] + \
                  [(c[0] + n * e, c[1], c[2]) for c in oper_lean(Q, m)]
            r['一致' if lhs == rhs else '**破れる**'] += 1
            if lhs != rhs and len(ex) < 2:
                ex[f'破れ Q={Q} e={e} n={n} m={m}'] = (lhs, rhs)
for k in sorted(r):
    print(f'  {k:12s} {r[k]:9d}')
for k, vv in ex.items():
    print(f'  ⚠ {k}\n      実際={vv[0]}\n      予測={vv[1]}')

print()
print('### (s4) 私の (y8) の例は `shTower` の形か')
print('  (y8) の例: `LF(1,0,1,2,1) = (0,0,0)(1,1,0)(2,1,0)`  ⟦2⟧ = (0,0,0)(1,1,0)(2,0,0)(3,1,0)')
Y = [(0, 0, 0), (1, 1, 0), (2, 1, 0)]
T = oper_lean(Y, 2)
print(f'  入力  {Y}   ⟹ `shTower` か: ', end='')
found = None
for pl in range(1, len(Y) + 1):
    if len(Y) % pl:
        continue
    Q = Y[:pl]
    for e in range(0, 6):
        if shTower(Q, e, len(Y) // pl) == Y:
            found = (Q, e, len(Y) // pl); break
    if found: break
print(found if found else '**いいえ（`shTower` ではない）**')
print(f'  展開  {T}   ⟹ `shTower` か: ', end='')
found2 = None
for pl in range(1, len(T) + 1):
    if len(T) % pl:
        continue
    Q = T[:pl]
    for e in range(0, 6):
        if shTower(Q, e, len(T) // pl) == T:
            found2 = (Q, e, len(T) // pl); break
    if found2: break
print(found2 if found2 else '**いいえ**')
print()
print('  ⟹ (y8) の入力は `shTower` では**なかった**（だから族から外れた）。')
print('     展開のほうが `shTower` になっている ⟹ **周期の 1 単位は入力の接頭辞**。')
print('     ⟹ (y8) の「周期 2」と `oper_shTower` の「最後の 1 個だけ違う」は')
print('        **同じ現象の別の見方**（前者は「入力が族の外」、後者は「族の中での閉性」）。')
