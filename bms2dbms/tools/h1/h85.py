# -*- coding: utf-8 -*-
"""**(k2) 補: `z = 1` が空虚に見えたのは箱の作為か（教訓 27）。**

h84.py の箱は 行2 < 2 なので **`zle1 R`（`Wset.lean:2470`: ∀p∈M, p.2.2 <= 1）を
黙って課していた**。そして `L105Cap.lean:3840` `towerExpBigZ_srow2_z_zero` は
**まさに `zle1 R` の下で `srow = 2` ⟹ `z = 0`** を（緑で）言っている。
⟹ h84 の「z=1 が 0 件」は新しい証拠ではなく、既知の定理の再現にすぎない。

⚠ **`LiftTowerExp2`（`Wset.lean:4046`）は `zle1 R` を仮定していない**
（`argOK R` は 行 0 の条件。`Wset.lean:1314`）。
しかも `Infcex.cexM = [(1,0,2),(2,0,0)]` のように 行2 = 2 の文脈は
このプロジェクトで実際に使われている。

⟹ **箱を 行2 < 3 に広げて `z = 1` が本当に出るかを見る。**
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import fmt, entry, srow, has_parent, dom_m, argOK, Lift1

ref = wref.Ref(maxnodes=4000)


def run(cmax, lens, tmax=2, vmax=3):
    cols = [(d, b, c) for d in range(1, 3) for b in range(3) for c in range(cmax)]
    print('### 箱: 行2 < %d（`zle1 R` を %s）、`|R|` = %s'
          % (cmax, '課す' if cmax <= 2 else '**課さない**', list(lens)))
    print()
    print('| `|R|` | `z` | **分母** | `h2` 成立 | `h2` 率 | 例 |')
    print('|--:|--:|--:|--:|--:|---|')
    for L in lens:
        for z in (0, 1):
            den = ok = 0
            ex = None
            for R in itertools.product(cols, repeat=L):
                R = list(R)
                if not argOK(R) or dom_m(R) is None:
                    continue
                if srow(R, len(R) - 1) != 2:
                    continue
                for v in range(vmax):
                    if not has_parent([(0, v, z)] + R, 2, len(R)):
                        continue
                    for t in range(tmax):
                        Q = Lift1([(0, v, z)] + R[:-1], t)
                        if ref.inW(Q, 2 * (v + t) + z) is not True:
                            continue
                        den += 1
                        f = all(has_parent(Q[:j + 1], 2, j)
                                for j in range(len(Q)) if entry(Q, 2, j) > 0)
                        ok += f
                        if not f and ex is None:
                            ex = (R, v, t, Q)
            s = ('R=`%s` v=%d t=%d Q=`%s`' % (fmt(ex[0]), ex[1], ex[2], fmt(ex[3]))
                 if ex else '—')
            print('| %d | %d | **%d** | %d | **%.1f%%** | %s |'
                  % (L, z, den, ok, 100.0 * ok / max(den, 1), s))
    print()


if __name__ == '__main__':
    print('## (k2) 補: `z = 1` は箱の作為か（教訓 27）')
    print()
    run(2, (2, 3))
    run(3, (2, 3))
