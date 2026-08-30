# -*- coding: utf-8 -*-
"""**課題 R100（team-lead 番号。私の §R100 の続きなので §R100-b とする）
—— 1 列の `TowerGraft2` を完全に書き下す。L3 の課題 L120 の足場。**

主語  `S = (0,v,z)(d,b,c)`
与件  `d >= 1`（argOK）, `c >= 1`（srow=2）, `v < b`, `z < c`, `z <= 1`,
      `domT R m`（`R = [(d,b,c)]`, `lev R 0 = 2b + c = m+1`）,
      `hasParent S (srow S 1) 1`

⚠ **`Trio.lean:98` の `oper` を使う**（`trio.py` の `expand` は長さ 1 で `[]` を返す。R98 の罠）。
⚠ 所属は R94 より**反証できない**。`ok` は健全（木が長さ <= 1 に落ち切った証拠）、
   `unknown` は「未定」であって「偽の証拠」ではない。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r98 import oper_lean
from r89 import inW


def lev(c):
    return 2 * c[1] + c[2]


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def graft(M, y):
    """`Wset.lean:67`。`M.dropLast ++ y.map (·.1 + entry M 0 (|M|-1))`。"""
    dd = M[-1][0] if M else 0
    return M[:-1] + [(p[0] + dd, p[1], p[2]) for p in y]


def shape(S):
    """`oper` の `j0 / i1 / d0 / d1`（`Trio.lean:98` の逐語）。"""
    j1 = len(S) - 1
    i1 = srow(S, j1)
    j0 = trio.parent(S, i1, j1)
    if j0 is None:
        return (None, i1, 0, 0)
    d0 = (S[j1][0] - S[j0][0]) if i1 > 0 else 0
    d1 = (S[j1][1] - S[j0][1]) if i1 > 1 else 0
    return (j0, i1, d0, d1)


FAM = [(d, b, c, v, z)
       for d in (1, 2, 3) for b in (1, 2, 3, 4) for c in (1, 2, 3)
       for v in range(b) for z in range(min(c, 2))]

print('### R100-b 1 列の `TowerGraft2` を書き下す')
print()
print('## (y1) `S⟦n⟧` —— `j0` / `i1` / `d0` / `d1` と塔の形')
tot = Counter(); bad = []
for (d, b, c, v, z) in FAM:
    S = [(0, v, z), (d, b, c)]
    j0, i1, d0, d1 = shape(S)
    tot[f'j0={j0} i1={i1} d0={"d" if d0 == d else d0} '
        f'd1={"b-v" if d1 == b - v else d1}'] += 1
    for n in range(1, 8):
        T = oper_lean(S, n)
        pred = [(k * d, v + k * (b - v), z) for k in range(n)]
        tot['塔 = 等差ラダー/' + ('ok' if T == pred else '**VIOL**')] += 1
        if T != pred and len(bad) < 3:
            bad.append((d, b, c, v, z, n, T, pred))
for k in sorted(tot):
    print(f'  {k:44s} {tot[k]:8d}')
for x in bad:
    print(f'  ⚠ {x}')
print(f'  ⟹ 族 {len(FAM)} 個すべてで **j0 = 0, i1 = 2, d0 = d, d1 = b - v**')
print('     `range\' j0 (j1-j0) = range\' 0 1 = [0]` ⟹ 写しは**根 1 列だけ**')
print('     写し k = `(0 + k*d0, v + k*d1, z)`（`le0 S 0 0` も `le1 S 0 0` も反射で真）')
print('     ⟹ **`S⟦n⟧ = [(k*d, v + k*(b-v), z) | k < n]`**')
print()

print('## (y2) 節 3 の義務 `∀ y ∈ W m, based y → graft R y ∈ Wstar` の具体形')
print('  `R = [(d,b,c)]` なので `R.dropLast = []`、`entry R 0 (|R|-1) = d`')
g = Counter()
for (d, b, c, v, z) in FAM[:40]:
    for _ in range(30):
        import random
        rng = random.Random(d * 1000 + b * 100 + c * 10 + v + z)
        L = rng.randint(0, 4)
        y = [(0, rng.randint(0, 3), rng.randint(0, 2))] + \
            [(rng.randint(0, 3), rng.randint(0, 3), rng.randint(0, 2))
             for _ in range(L)]
        gr = graft([(d, b, c)], y)
        sh = [(p[0] + d, p[1], p[2]) for p in y]
        g['graft R y = shiftr01 d 0 y/' + ('ok' if gr == sh else '**VIOL**')] += 1
        g['argOK (graft R y)/' + ('ok' if all(q[0] >= 1 for q in gr) else '**VIOL**')] += 1
for k in sorted(g):
    print(f'  {k:40s} {g[k]:8d}')
print('  ⟹ **`graft [(d,b,c)] y = shiftr01 d 0 y`**（行 0 を `d` だけ下げるだけ）')
print('     `based y`（`entry y 0 0 = 0`）＋ `d >= 1` ⟹ **`argOK` は自動**')
print('  ⟹ 義務の展開形:')
print('     **∀ based y ∈ W m, ∀ v\' z\' a\', z\'<=1 → 2v\'+z\'<=a\' →')
print('        `(0,v\',z\') :: shiftr01 d 0 y ∈ W a\'`**')
print()

print('## (y3) `m = 2b + c - 1`。`y` はどこまで大きくなれるか')
for (d, b, c) in ((1, 1, 1), (1, 2, 1), (1, 2, 2), (2, 3, 1)):
    m = 2 * b + c - 1
    roots = [(0, y1, y2) for y1 in range(0, m + 1) for y2 in range(0, m + 1)
             if 2 * y1 + y2 <= m]
    print(f'  d={d} b={b} c={c} ⟹ m = 2b+c-1 = {m}；'
          f'`based y` の根は `lev y 0 <= m`（`lev_root_le_of_mem_W`、緑）')
    print(f'     ⟹ 根の候補 {len(roots)} 個: {roots}')


print()
print('## (y4) 最小の生きた例 `(0,0,0)(1,1,1)`（`v=z=0, d=b=c=1, m=2`）を完全に書き下す')
S0 = [(0, 0, 0), (1, 1, 1)]
print(f'  S = {S0}   d=1, b=1, c=1, v=0, z=0, m = 2b+c-1 = 2')
j0, i1, d0, d1 = shape(S0)
print(f'  `oper` の分岐: j0={j0}, i1=srow={i1}, d0={d0}, d1={d1}')
for n in range(1, 7):
    print(f'    S⟦{n}⟧ = {oper_lean(S0, n)}')
print('  ⟹ **S⟦n⟧ = (0,0,0)(1,1,0)(2,2,0)…((n-1),(n-1),0)** —— 行 2 は 1 段で 0 に潰れる')
print()
print('  節 3 の義務（`R = [(1,1,1)]`, `m = 2`）:')
print('    **∀ based y ∈ W 2, ∀ v\' z\' a\', z\'<=1 → 2v\'+z\'<=a\' →')
print('       `(0,v\',z\') :: shiftr01 1 0 y ∈ W a\'`**')
print()

print('## ★ (y5) `oper_cons_tower2` を回すと債務は何になるか（新規）')
print('  `oper_cons_tower2`（`Wset.lean:3231`、緑）:')
print('    `((0,v,z)::R)⟦n+1⟧ = (0,v,z) :: graft R (Lift1 (((0,v,z)::R)⟦n⟧) (b - v))`')
print('  ⟹ 節 3 の義務を当てるには **`Lift1 T_n (b-v) ∈ W m` と `based`** が要る（`T_n = S⟦n⟧`）')
print()
lift_chk = Counter(); ex2 = {}
for (d, b, c, v, z) in FAM:
    m = 2 * b + c - 1
    for n in range(1, 7):
        T = oper_lean([(0, v, z), (d, b, c)], n)
        X = [(cc[0], cc[1] + ((b - v) if trio.is_ancestor(T, 1, 0, i) else 0), cc[2])
             for i, cc in enumerate(T)]
        uni = [(cc[0], cc[1] + (b - v), cc[2]) for cc in T]
        lift_chk['Lift1 T_n (b-v) = 一様シフト/' +
                 ('ok' if X == uni else '**VIOL**')] += 1
        pred = [(k * d, b + k * (b - v), z) for k in range(n)]
        lift_chk['= [(k*d, b + k*(b-v), z)]/' + ('ok' if X == pred else '**VIOL**')] += 1
        lift_chk['based (Lift1 T_n)/' + ('ok' if X[0][0] == 0 else '**VIOL**')] += 1
        lift_chk['lev(root) <= m/' + ('ok' if lev(X[0]) <= m else '**VIOL**')] += 1
        if lev(X[0]) > m:
            ex2.setdefault('lev>m', (d, b, c, v, z, n, X[0], m))
for k in sorted(lift_chk):
    print(f'  {k:42s} {lift_chk[k]:8d}')
print('  ⟹ `T_n` は行 0 が公差 `d` で狭義増加 ⟹ 行 0 祖先鎖は `j → j-1 → … → 0`')
print('     `k>=1` の列の行 1 は `v + k*(b-v) > v` ⟹ **全列が錐に入る**')
print('     ⟹ **`Lift1 T_n (b-v)` は一様シフトそのもの** ＝ `[(k*d, b + k*(b-v), z)]`')
print('     根は `(0, b, z)`、`lev = 2b + z`。`m = 2b+c-1` なので')
print('     **`lev <= m ⟺ z < c`** ＝ **場面の条件そのもの**（`tower2_zr`）')
print()
print('## ★★ (y6) ⟹ 本当の債務は 1 つの等差ラダー')
print('  `Ladder(d, w, e, z, n) := [(k*d, w + k*e, z) | k < n]`  （`d>=1, e>=1`）')
print('  債務: **`Ladder(d, w, e, z, n) ∈ W (2w + z)`**')
lad = Counter(); memo = {}
for d in (1, 2, 3):
    for w in range(0, 4):
        for e in (1, 2, 3):
            for z in (0, 1):
                for n in range(1, 8):
                    L = [(k * d, w + k * e, z) for k in range(n)]
                    r = inW(L, 2 * w + z, 11, memo, 34)
                    lad[f'z={z}/' + ('ok' if r is True else
                                     'VIOL' if r is False else 'unknown')] += 1
for k in sorted(lad):
    print(f'  {k:20s} {lad[k]:8d}')
print()
print('  なぜ `z=1` が易しいか（算術）: 全列の行 2 が `z=1` ⟹ `srow=2` だが')
print('    `nextrel2` は行 2 が真に小さい祖先を要求 ⟹ **親が無い** ⟹ `Pred`（1 列ずつ減る）')
print('  なぜ `z=0` が本体か: `srow=1` で行 1 の親は 1 つ手前 ⟹ `j0 = n-2 >= 1`')
print('    ⟹ **cons 保存の枝**（`oper_cons_nat`）。長さは伸びるが行 1 が凍る')


print()
print('## ★★★ (y7) `z=0` のラダーの展開を書き下す（L3 の帰納の目標）')
rec = Counter(); exr = {}
for d in (1, 2, 3):
    for w in range(0, 4):
        for e in (1, 2, 3):
            for n in range(2, 9):
                L = [(k * d, w + k * e, 0) for k in range(n)]
                j0, i1, d0, d1 = shape(L)
                rec[f'n={n}: j0={"n-2" if j0 == n - 2 else j0} i1={i1} '
                    f'd0={"d" if d0 == d else d0} d1={d1}'] += 1
                for nn in (1, 2, 3):
                    T = oper_lean(L, nn)
                    if n == 2:
                        pred = [(k * d, w, 0) for k in range(nn)]     # 平坦ラダー
                    else:
                        pred = L[:n - 2] + [((n - 2 + k) * d, w + (n - 2) * e, 0)
                                            for k in range(nn)]
                    rec['展開の形/' + ('ok' if T == pred else '**VIOL**')] += 1
                    if T != pred:
                        exr.setdefault('形の違反', (d, w, e, n, nn, T, pred))
for k in sorted(rec):
    print(f'  {k:40s} {rec[k]:8d}')
for k in sorted(exr):
    print(f'  ⚠ {k}: {exr[k]}')
print()
print('  ⟹ **n = 2**: `j0 = 0` の根の塔だが `d1 = 0` ⟹ 写しは行 1 が `w` で凍った平坦ラダー')
print('       `[(k*d, w, 0)]` は行 1 が全部 `w` ⟹ 行 1 の親が無い ⟹ `Pred` で 1 列ずつ減る')
print('       ⟹ **`Ladder(d,w,e,0,2)` は無条件で `W (2w)` に落ちる**')
print('  ⟹ **n >= 3**: `j0 = n-2 >= 1` ⟹ **cons 保存**（`oper_cons_nat`）。')
print('       `Ladder⟦n\'⟧ = Ladder(d,w,e,0,n-2) ++ [((n-2+k)d, w+(n-2)e, 0) | k<n\']`')
print('       ＝ **短いラダー ＋ 行 1 が凍った平坦な尾**')
print('       ⟹ 長さの帰納ではなく **`n`（ラダーの段数）の帰納**が回る')


print()
print('## ★★★★ (y8) 展開で閉じる族を探す —— `LF(d,w,e,n,t)`')
print('  `LF(d,w,e,n,t) := [(k*d, w+k*e, 0) | k<n] ++ [((n-1+j)*d, w+(n-1)*e, 0) | 1<=j<=t]`')
print('    ＝ **`n` 段のラダー ＋ 最終段の行 1 で凍った `t` 本の平坦な尾**')
print('  （`Ladder(d,w,e,0,n) = LF(d,w,e,n,0)`）')


def LF(d, w, e, n, t):
    out = [(k * d, w + k * e, 0) for k in range(n)]
    out += [((n - 1 + j) * d, w + (n - 1) * e, 0) for j in range(1, t + 1)]
    return out


cl = Counter(); exc = {}
for d in (1, 2, 3):
    for w in range(0, 4):
        for e in (1, 2, 3):
            for n in range(1, 7):
                for t in range(0, 5):
                    L = LF(d, w, e, n, t)
                    if len(L) < 2:
                        continue
                    for nn in (1, 2, 3, 4):
                        T = oper_lean(L, nn)
                        hit = None
                        for n2 in range(0, n + 2):
                            for t2 in range(0, len(T) + 2):
                                if LF(d, w, e, n2, t2) == T:
                                    hit = (n2, t2); break
                            if hit: break
                        cl['族に留まる/' + ('ok' if hit else '**外れる**')] += 1
                        if hit:
                            cl[f'  遷移 (n,t)->(n2,t2): '
                               f'n2={"n" if hit[0] == n else "n-1" if hit[0] == n - 1 else hit[0]}'] += 1
                        elif len(exc) < 3:
                            exc[f'外れる {(d,w,e,n,t,nn)}'] = T
for k in sorted(cl):
    print(f'  {k:44s} {cl[k]:8d}')
for k, vv in exc.items():
    print(f'  ⚠ {k}: {vv}')
