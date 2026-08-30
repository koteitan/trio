# -*- coding: utf-8 -*-
"""**(NC-2) L3 §302 の形の裏取り ＋ (FIX-1) タイの `Lift1` を母集団に入れる。**

## ⚠ 逐語（`Trio.lean:60`）

    nextrel2 M j0 j1 := j0 < |M| ∧ j1 < |M| ∧ j0 < j1 ∧ entry M 2 j0 < entry M 2 j1
                        ∧ le1 M j0 j1
                        ∧ (∀ j, j0 < j ∧ le1 M j j1 → entry M 2 j1 <= entry M 2 j)

## (NC-2) L3 §302 の主張

    `z <= 1` では `nextrel2` の親は `z = 0` の列、的は `z = 1`      … 算術（`entry 2 j0 < entry 2 j1 <= 1`）
    **`z = 0` の列がどれも末尾の `le1` 錐の外 ⟹ 行 2 の親は無い（＝ 残差）**
    ⟹ ★ 測るのは **A := 孤児（`srow=2`）** と **B := `∀ y, entry Q 2 y = 0 → ¬ le1 Q y (|Q|-1)`** の一致

## (FIX-1) 母集団の穴を塞ぐ

    ⛔ `Reach+` の持ち上げ 4 本は **どれもタイのある `X` を除外**（狭義／無タイ／TieFree／行2≡0）。
      ⚠ 正確には **行2≡0 の枝だけはタイを除外しません**が、私は `X[0][0] = 0` を余計に課していました。
    ⟹ ★ 直し: **`L105.liftStage_of_zeroRow2`（仮定ゼロ）は根の行 0 に条件が無い**
      ⟹ **行 2 ≡ 0 の `X`（タイの有無に関わらず）の `Lift1 X d` を全部入れる** ⟹ 健全

## ⚠ 測る前の見積もり

    (NC-2) **100%**（`nextrel2` の定義の展開なので）。⟹ ★ 対照で空虚でないことを示す。
    (FIX-1) **破れが出る**（H12 の `w71Ctr = [(0,2,0),(1,1,0)]` がその形）。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r260 import reach
from r315 import windows, hr0s

pct = lambda a, b: 100.0 * a / b if b else float('nan')
le1 = lambda Q, y, j: trio.is_ancestor(Q, 1, y, j)


def orphan(Q):
    j = len(Q) - 1
    return trio.parent(Q, srow(Q, j), j) is None


def outside(Q):
    """B := `z = 0` の列がどれも末尾の `le1` 錐の外。"""
    j = len(Q) - 1
    return all(not le1(Q, y, j) for y in range(len(Q)) if Q[y][2] == 0)


def nc2(QS, tag):
    G = Counter(); ex = []
    for Q in QS:
        if len(Q) < 2 or not hr0s(Q): continue
        if srow(Q, len(Q) - 1) != 2: continue
        G['n'] += 1
        A = orphan(Q); B = outside(Q)
        G['A 孤児'] += A; G['B 錐の外'] += B
        G['★ A ⟺ B'] += (A == B)
        G['⛔ A ∧ ¬B'] += (A and not B)
        G['⛔ ¬A ∧ B'] += ((not A) and B)
        if A != B and len(ex) < 3: ex.append((Q, A, B))
        if A:
            zs = [y for y in range(len(Q)) if Q[y][2] == 0]
            G['残差: z=0 の列が 0 本'] += (len(zs) == 0)
            G['残差: z=0 の列が 1 本'] += (len(zs) == 1)
            G['残差: z=0 の列が 2 本以上'] += (len(zs) >= 2)
            if zs:
                d = len(Q) - 1 - max(zs)
                G['残差: 最も近い z=0 との距離 %s' % (d if d <= 3 else '>=4')] += 1
    n = G['n']
    print('  [%s] `hr0` ∧ `srow(末尾)=2` の分母 %d' % (tag, n))
    if not n: return
    print('     A 孤児 %.4f%% / B 錐の外 %.4f%% / ★ A ⟺ B %.4f%% | ⛔ A∧¬B %d 件 / ⛔ ¬A∧B %d 件'
          % (pct(G['A 孤児'], n), pct(G['B 錐の外'], n), pct(G['★ A ⟺ B'], n), G['⛔ A ∧ ¬B'], G['⛔ ¬A ∧ B']))
    m = G['A 孤児']
    if m:
        print('     残差 %d 件の `z = 0` の列: 0 本 %.4f%% / 1 本 %.4f%% / 2 本以上 %.4f%%'
              % (m, pct(G['残差: z=0 の列が 0 本'], m), pct(G['残差: z=0 の列が 1 本'], m), pct(G['残差: z=0 の列が 2 本以上'], m)))
        print('     　最も近い z=0 との距離: 1 が %.4f%% / 2 が %.4f%% / 3 が %.4f%% / >=4 が %.4f%%'
              % (pct(G['残差: 最も近い z=0 との距離 1'], m), pct(G['残差: 最も近い z=0 との距離 2'], m),
                 pct(G['残差: 最も近い z=0 との距離 3'], m), pct(G['残差: 最も近い z=0 との距離 >=4'], m)))
    for (Q, A, B) in ex:
        print('     ⛔ 破れ: A=%s B=%s  %s' % (A, B, ' '.join('(%d,%d,%d)' % q for q in Q[:9])))


print('=== (NC-2) L3 §302 の裏取り ===')
t0 = time.time()
SH = [[tuple(v) for v in M] for M in load()]
SHW = list(windows(SH))
nc2(SHW, 'シートの窓（健全 W_drop+W_take）')
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
RCW = list(windows([list(x) for x in RC], cap=200000))
nc2(RCW, 'Reach の窓（健全）')
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 3) for z in (0, 1)]
nc2([list(t) for t in itertools.product(COL, repeat=3)], '⛔ 負の対照: 人工 3 列')
nc2([list(t) for t in itertools.product(COL, repeat=4)][:200000], '⛔ 負の対照: 人工 4 列 20 万本')

print()
print('=== (FIX-1) タイのある `X`（行 2 ≡ 0）の `Lift1` を足す ===')
base = SHW + RCW
tie = [Q for Q in base if all(p[2] == 0 for p in Q) and any(Q[j][1] == Q[0][1] for j in range(1, len(Q)))]
print('  行 2 ≡ 0 かつタイのある `X`: %d 本（健全な `W` の元）' % len(tie))
add = []
for X in tie:
    for d in (1, 2):
        add.append([(c[0], c[1] + (d if trio.is_ancestor(X, 1, 0, i) else 0), c[2]) for i, c in enumerate(X)])
print('  ⟹ `liftStage_of_zeroRow2`（仮定ゼロ）で **健全に** %d 本追加' % len(add))

for tag, QS in (('元の箱（窓のみ）', base), ('★ (FIX-1) 追加後', base + add), ('★ 追加分だけ', add)):
    c = Counter()
    for Q in QS:
        if len(Q) < 2 or not hr0s(Q): continue
        s = srow(Q, len(Q) - 1)
        if s < 1 or not orphan(Q): continue
        c['残差B'] += 1
        c['末尾行1 = 根'] += (Q[-1][1] == Q[0][1])
        c['末尾行1 > 根'] += (Q[-1][1] > Q[0][1])
        c['⛔ 末尾行1 < 根'] += (Q[-1][1] < Q[0][1])
    n = c['残差B']
    print('  [%-18s] 残差B %6d 件 | 末尾行1=根 %8.4f%% / >根 %8.4f%% / ⛔ <根 %8.4f%%'
          % (tag, n, pct(c['末尾行1 = 根'], n), pct(c['末尾行1 > 根'], n), pct(c['⛔ 末尾行1 < 根'], n)))
print('（%.1f 秒）' % (time.time() - t0))
