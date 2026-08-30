# -*- coding: utf-8 -*-
"""**(R1R0-KILL) ＋ (RSUM1')。**

## ⚠ 母集団を 1 行で（L3 の 1,496 / 13,712 の再現を狙う）

`psiI.json` の DBMS 列 1,637 行列（`|M| <= 8`、行 2 <= 1）について
`B = M[:j+1]`、`s = srow(B,j) >= 1`、`p = parent(B,s,j)`、`j-p >= 2` の窓 `V = B[p:j]` で
**`hr0(V)` かつ `hz0(V)`** のもの。**分母 ＝ その窓の「行 2 = 0 かつ行 1 > 0」の列**、
**分子 ＝ そのうち行 1 の親が無い列（＝ 行 1 の孤児）**。

## 測るもの

    **(R1R0-KILL)** その孤児で **`R1<=R0(V)`** が成り立つか（★ 対照 ＝ 窓の全列）
      ⟹ ⛔ **偽なら `R1<=R0` が残差を殺します**（本命の確定）
    **(RSUM1')** **`T` の根（＝ `V` の根）の `le0` 祖先の鎖**の上に、
      **行 1 が `entry V 1 0` より小さい列**があるか
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import trio
from collections import Counter
from r126 import srow
from r263 import load
from r269 import R1R0, norm


def chain0(B, p):
    """`p` から行 0 の親を辿る鎖（`nextrel0` の親は一意）。"""
    out = []; y = p
    while True:
        y = trio.parent(B[:y + 1], 0, y)
        if y is None: break
        out.append(y)
    return out


def run(LMAX, tag):
    t0 = time.time(); c = Counter(); ex = []
    for M in load():
        if len(M) > LMAX or any(x[2] > 1 for x in M): continue
        for j in range(2, len(M)):
            B = [tuple(v) for v in M[:j + 1]]
            s = srow(B, j)
            if s == 0: continue
            p = trio.parent(B, s, j)
            if p is None or j - p < 2: continue
            V = [tuple(v) for v in B[p:j]]
            # hr0(V) ∧ hz0(V)
            if V[0][2] != 0: continue
            if not all(V[0][0] < V[l][0] for l in range(1, len(V))): continue
            r1 = R1R0(V); r1n = R1R0(norm(V))
            for t in range(1, len(V)):
                if V[t][2] != 0 or V[t][1] == 0: continue
                c['★ 対照（窓の全列: 行2=0 ∧ 行1>0）'] += 1
                if r1:  c['   (対照) R1<=R0（正規化なし）'] += 1
                if r1n: c['   (対照) R1<=R0（正規化あり）'] += 1
                if trio.parent(V[:t + 1], 1, t) is not None: continue
                c['★★ (R1R0-KILL) 分母（行 1 の孤児）'] += 1
                if r1:
                    c['⛔ **孤児で R1<=R0 が真（正規化なし）**'] += 1
                    if len(ex) < 4: ex.append(('R1真', B, p, V, t))
                else: c['★★★ **孤児で R1<=R0 が偽 ⟹ 殺せる（正規化なし）**'] += 1
                if r1n: c['⛔ 孤児で R1<=R0 が真（正規化あり）'] += 1
                else:   c['★ 孤児で R1<=R0 が偽（正規化あり）'] += 1
                # ---------- (RSUM1') ----------
                ch = chain0(B, p)
                c['(RSUM1d) 分母'] += 1
                if any(B[y][1] < V[0][1] for y in ch):
                    c['★★ (RSUM1d) 鎖上に下の列あり'] += 1
                else:
                    c['⛔ (RSUM1d) 鎖上に無し'] += 1
                c[f'   鎖の長さ {min(len(ch),5)}'] += 1
                if ch: c[f'   鎖の上の行 1 の最小値 - V の根の行 1 = '
                         f'{min(B[y][1] for y in ch) - V[0][1]}'] += 1
    def pc(x, y): return f'{x} ({100*x/max(y,1):8.4f}%)'
    d0 = c['★ 対照（窓の全列: 行2=0 ∧ 行1>0）']
    d1 = c['★★ (R1R0-KILL) 分母（行 1 の孤児）']
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    print(f'  ★ **対照（窓の全列）{d0}**  R1<=R0（正規化なし）'
          f'{pc(c["   (対照) R1<=R0（正規化なし）"], d0)}  '
          f'（正規化あり）{pc(c["   (対照) R1<=R0（正規化あり）"], d0)}')
    print(f'  ★★ **(R1R0-KILL) 分母（行 1 の孤児）{d1}** ＝ {pc(d1, d0)}')
    print(f'      ★★★ **孤児で R1<=R0 が偽 ⟹ 殺せる**（正規化なし）'
          f'{pc(c["★★★ **孤児で R1<=R0 が偽 ⟹ 殺せる（正規化なし）**"], d1)}   '
          f'⛔ **真（殺せない）** {pc(c["⛔ **孤児で R1<=R0 が真（正規化なし）**"], d1)}')
    print(f'      （正規化あり）偽 {pc(c["★ 孤児で R1<=R0 が偽（正規化あり）"], d1)}   '
          f'⛔ 真 {pc(c["⛔ 孤児で R1<=R0 が真（正規化あり）"], d1)}')
    d2 = c["(RSUM1') 分母"]
    print(f'  ★★ (RSUM1d) 分母 {d2}  ★★ **鎖の上に「行 1 が下」の列がある** '
          f'{pc(c["★★ (RSUM1d) 鎖上に下の列あり"], d2)}   '
          f'⛔ 無い {c["⛔ (RSUM1d) 鎖上に無し"]}')
    for k in sorted(c):
        if k.startswith('   鎖'): print(f'      {k}: {c[k]}')
    for x in ex: print(f'      ⛔ {x[0]}: B={x[1]} p={x[2]} V={x[3]} t={x[4]}')
    print()


if __name__ == '__main__':
    run(8, '★ シート（|M|<=8、行2<=1）— L3 の 1,496/13,712 の再現')
    run(10**9, '★★ シート全体（箱を伸ばす）')
