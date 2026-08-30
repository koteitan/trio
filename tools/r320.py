# -*- coding: utf-8 -*-
"""**(W74-M) —— `srow = 2` の残核は、塔を積むと行 2 の親を得るか。**

## ⚠ 逐語

    `mTower Q d0 d1 n = (List.range n).flatMap fun k => Lift1 (shiftr01 (d0*k) 0 Q) (d1*k)`
                                                                    （`L105Cap.lean:4177`）
    L3 §303（緑、`z ≤ 1` で必要十分）:
      **`hasParent M 2 t ↔ ∃ c, c < t ∧ entry M 2 c = 0 ∧ le1 M c t`**

## ⚠ 母集団（除外条件）

    `Reach` の窓 `M[j:k]`（`Wtower2.W_drop` `:2870` ＋ `Wset.W_take`、**健全**）から、
    **`hr0 Q` ∧ `srow(末尾) = 2` ∧ 孤児**（＝ 残差、1,387 件）
    と、そのうち **行 2 が混在**する群（＝ 本当の残核、1,006 件）。
    `d ∈ {0,1,2}`、`e ∈ {0,1,2}`、`n ∈ {1,2,3}`。**`W` の判定は不要**（列の条件だけ）。

## ⚠ 測る前の見積もり

    ★ `e > 0` … **70〜100% が親を得る**（H12 の予測どおりなら）
    ★ `e = 0` … **0%**（錐が動かないので、対照として残るはず）
    ★ `n = 1` … `mTower Q d e 1 = Q` なので **必ず孤児**（検算）
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r260 import reach
from r315 import windows, hr0s

pct = lambda a, b: 100.0 * a / b if b else float('nan')
le1 = lambda M, y, j: trio.is_ancestor(M, 1, y, j)
mixed2 = lambda Q: any(p[2] == 0 for p in Q) and any(p[2] > 0 for p in Q)


def hasp2(M):
    """L3 §303 の右辺。"""
    t = len(M) - 1
    return any(M[c][2] == 0 and le1(M, c, t) for c in range(t))


t0 = time.time()
RC = set()
for vs, ns, depth in (((1, 2, 3, 4), (1, 2, 3), 5), ((1, 2, 3, 4, 5, 6), (1, 2, 3), 6)):
    RC |= reach(vs, ns, depth)
res = []
for Q in windows([list(x) for x in RC], cap=200000):
    if len(Q) < 2 or not hr0s(Q): continue
    if srow(Q, len(Q) - 1) != 2: continue
    if trio.parent(Q, 2, len(Q) - 1) is not None: continue
    res.append(Q)
core = [Q for Q in res if mixed2(Q)]
print('== 母集団 ==')
print('  `srow=2` の残差: %d 件 ／ うち行 2 混在（本当の残核）: %d 件' % (len(res), len(core)))

print()
print('== (W74-M) `mTower Q d e n` の末尾は行 2 の親を持つか ==')
print('%-6s %-4s %-4s %10s %14s | %10s %14s' % ('n', 'd', 'e', '残差 分母', '★ 親を得る', '残核 分母', '★ 親を得る'))
chk = Counter()
for n in (1, 2, 3):
    for d in (0, 1, 2):
        for e in (0, 1, 2):
            c1 = c2 = 0
            for Q in res:
                M = mTower(Q, d, e, n)
                if len(M) < 2: continue
                got = hasp2(M)
                # L3 §303 の検算（parent との一致）
                chk['n'] += 1
                chk['一致'] += (got == (trio.parent(M, 2, len(M) - 1) is not None) if srow(M, len(M) - 1) == 2 else True)
                if got: c1 += 1
            for Q in core:
                M = mTower(Q, d, e, n)
                if len(M) < 2: continue
                if hasp2(M): c2 += 1
            print('%-6d %-4d %-4d %10d %13.4f%% | %10d %13.4f%%'
                  % (n, d, e, len(res), pct(c1, len(res)), len(core), pct(c2, len(core))))
print()
print('  ⚠ L3 §303（`hasParent M 2 t ↔ ∃c, z=0 ∧ le1`）の検算: %d / %d = %.4f%%'
      % (chk['一致'], chk['n'], pct(chk['一致'], chk['n'])))

print()
print('== ⛔ `e > 0` でも親を得ない `Q`（先頭 5 件、n=2, d=1, e=1）==')
bad = [Q for Q in core if not hasp2(mTower(Q, 1, 1, 2))]
print('  件数 %d / %d = %.4f%%' % (len(bad), len(core), pct(len(bad), len(core))))
for Q in sorted(bad, key=len)[:5]:
    print('    |Q|=%d  %s' % (len(Q), ' '.join('(%d,%d,%d)' % q for q in Q)))

print()
print('== ★ 最小例 Q = (5,4,0) (6,3,1) の手計算の裏取り ==')
Q = [(5, 4, 0), (6, 3, 1)]
for (d, e, n) in ((1, 1, 2), (1, 1, 3), (1, 0, 2), (0, 1, 2), (1, 2, 2)):
    M = mTower(Q, d, e, n)
    print('   d=%d e=%d n=%d ⟹ M=%s  srow(末尾)=%d 親=%s（L3 §303 の右辺 %s）'
          % (d, e, n, ' '.join('(%d,%d,%d)' % q for q in M), srow(M, len(M) - 1),
             trio.parent(M, srow(M, len(M) - 1), len(M) - 1), hasp2(M)))
print('（%.1f 秒）' % (time.time() - t0))
