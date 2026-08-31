# -*- coding: utf-8 -*-
"""**(R-C1) `LiftOperComm`: `oper (Lift1 M t) n = Lift1 (oper M n) t` は成り立つか。**

## ⚠ 定義を逐語で写す（教訓 25 / 28）

    `Wset.lean:927`
      noncomputable def Lift1 (X : TrioSeq) (d : N) : TrioSeq :=
        (List.range X.length).map fun i =>
          ((entry X 0 i, **entry X 1 i + (if le1 X 0 i then d else 0)**, entry X 2 i))

    ⟹ ⛔ **`Lift1` が足すのは「行 1」です（行 0 ではありません）**。
      team-lead の伝言は「行 0 を +t」でしたが、**逐語では行 1** です。
      足す先は **根 `0` の `le1` 錐の中の列だけ**。行 0 と行 2 は動きません。

## ⚠ 既存定理（grep 済み。教訓 25 の再発防止）

    `Wset.oper_Lift1_root`（`Wset.lean:3384`）—— **右辺は `Lift1` ではなく `glift`**:
      (hL : |M|-1 ≠ 0) (hz : 末尾が全零でない)
      (hp : hasParent M (srow M (|M|-1)) (|M|-1))
      (hpar : **parent … = 0**（親が根）) (hcone : **le1 M 0 (|M|-1)**（末尾が錐の中）)
      ⟹ **`(Lift1 M t)⟦n⟧ = glift M (|M|-1) 0 t (M⟦n⟧)`**

⟹ ★ ですから **素朴な `LiftOperComm`（右辺が `Lift1`）は、たぶん偽**です。実測します。

## ⚠ 母集団と分け方

    シートの窓 ／ Reach の窓（`W_drop` ＋ `W_take`、**健全**、根が持ち上がる）／ ⛔ 人工総当たり
    `t ∈ {0,1,2,3}`、`n ∈ {1,2,3}`
    ⚠⚠ **`t = 0` は必ず別に数える**（自明に真 ⟹ 混ぜると偽の 100%）
    ⟹ ★ 分けて見る軸: **末尾が根の錐の中か**（`hcone`）／ **親が根か**（`hpar`）
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r263 import load
from r126 import srow
from r113 import Lift1
from r260 import reach
from r315 import windows

pct = lambda a, b: 100.0 * a / b if b else float('nan')


def ex(M, n):
    try: return [tuple(q) for q in trio.expand([list(q) for q in M], n)]
    except Exception: return None


def scan(MS, tag, TS=(0, 1, 2, 3), NS=(1, 2, 3)):
    G = {}; bad = []
    for M in MS:
        if len(M) < 2: continue
        t_ = len(M) - 1
        cone = trio.is_ancestor(M, 1, 0, t_)
        sr = srow(M, t_)
        par = trio.parent(M, sr, t_)
        for t in TS:
            for n in NS:
                L = Lift1(M, t)
                a = ex(L, n); b = ex(M, n)
                if a is None or b is None: continue
                ok = (a == Lift1(b, t) if b else a == b)
                keys = ['t=%d' % t]
                if t >= 1:
                    keys.append('★ t>=1 全')
                    keys.append('★ t>=1 / 末尾が錐の%s' % ('中' if cone else '外'))
                    keys.append('★ t>=1 / 親が根%s' % ('' if par == 0 else 'でない'))
                    if cone and par == 0: keys.append('★★ t>=1 / 錐の中 ∧ 親が根')
                for kk in keys:
                    g = G.setdefault(kk, Counter()); g['n'] += 1; g['ok'] += ok
                if t >= 1 and not ok and len(bad) < 4:
                    bad.append((M, t, n, a, Lift1(b, t), cone, par))
    print('  [%s]' % tag)
    for kk in ('t=0', 't=1', 't=2', 't=3', '★ t>=1 全', '★ t>=1 / 末尾が錐の中', '★ t>=1 / 末尾が錐の外',
               '★ t>=1 / 親が根', '★ t>=1 / 親が根でない', '★★ t>=1 / 錐の中 ∧ 親が根'):
        g = G.get(kk)
        if not g: continue
        print('     %-30s 分母 %8d  一致 %9.4f%%' % (kk, g['n'], pct(g['ok'], g['n'])))
    for (M, t, n, a, b, cone, par) in bad[:2]:
        print('     ⛔ 反例 t=%d n=%d 錐=%s 親=%s' % (t, n, cone, par))
        print('        M              = %s' % ' '.join('(%d,%d,%d)' % q for q in M))
        print('        (Lift1 M t)[n] = %s' % ' '.join('(%d,%d,%d)' % q for q in a))
        print('        Lift1 (M[n]) t = %s' % ' '.join('(%d,%d,%d)' % q for q in b))
    return G


t0 = time.time()
SH = [[tuple(v) for v in M] for M in load()]
scan(list(windows(SH)), 'シートの窓（健全 W_drop+W_take）')
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
scan(list(windows([list(x) for x in RC], cap=60000)), 'Reach の窓（健全）')
COL = [(a, b, z) for a in range(0, 4) for b in range(0, 3) for z in (0, 1)]
scan([list(t) for t in itertools.product(COL, repeat=3)], '⛔ 負の対照: 人工 3 列')
print('（%.1f 秒）' % (time.time() - t0))
