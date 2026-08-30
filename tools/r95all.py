# -*- coding: utf-8 -*-
"""**R95 全核版 —— `CORES.md` の全 32 核について「反証器が鳴りうるか」を判定する。**

判定基準（team-lead の指示どおり）:
  **結論の主語の根の `lev` が、前提から自動で結論の段以下になるか。**
  なる ⟹ **鳴りえない**（反証不能）。ならない ⟹ 鳴りうる（射程内）。

R94 の定理より、健全な反証器が確定 `False` を返す ⟺ `lev(主語) 0 > 段`。
使える必要条件は 1 本（`Wset.lean:2161` `lev_root_le_of_mem_W`、無条件・緑）:
  `X ∈ W m ∧ X ≠ [] ⟹ lev X 0 <= m`

各核について**前提の根の条件だけを満たす乱択データ**（＝本物の事例の**上位集合**）を作り、
結論の根の条件が破れるかを数える。上位集合で破れないなら本物でも絶対に破れない。

★ 結論が `∈ Wstar` / `∈ Wself` / `∈ GX` の核は**構造的に鳴りえない**（下の SHAPE 参照）。

読んだ定義（`file:line`）:
  `Wstar` `Wset:2684`  = `argOK R → ∀ v z a, z<=1 → 2v+z<=a → ((0,v,z)::R) ∈ W a`
                          ⟹ 主語の根は `(0,v,z)`、`lev = 2v+z <= a` は**前提そのもの**
  `Wself` `Wtower2:2987` = `M ∈ W (lev M 0)` ⟹ `lev M 0 <= lev M 0` は自明
  `GX`    `Gamma:169`   = `… Lift1 ((0,v,z) :: graft M (y.take i)) t ∈ W a`、`2(v+t)+z <= a`
                          ⟹ 根は `(0,v+t,z)`、`lev = 2(v+t)+z <= a` は前提そのもの
  `Lift1` `Wset:927`    根は `le1 X 0 0` が反射で成立 ⟹ **根の行 1 は必ず `+d`**
  `mliftR` `L53Subst:2719` `coneVR X w 0` は `coneVR_zero`（緑）で**常に真** ⟹ 根は必ず `+d`
  `mlift`  `Cgraft:312`  `coneV A v 0` ⟺ `v < entry A 1 0`。`Row1DownLocal` は
                          `v = entry X 1 0 - 1` かつ `1 <= entry X 1 0` ⟹ **常に真** ⟹ 根は `+d`
  `shiftr01 d0 d1` `Cnf:626` 根は `(+d0, +d1, 同)`
  `shTower Q e n` `Wtower2:1688` = `flatMap k<n, shiftr01 (k*e) 0 Q` ⟹ 根は `k=0` の `Q[0]`
  `oper` `Trio:98`      **第 1 列を絶対に落とさない**（R94）⟹ `M⟦n⟧` の根は `M[0]`
"""
import random
from collections import Counter

rng = random.Random(20260830)


def lev(c):
    return 2 * c[1] + c[2]


def rnd_col(dmin=0):
    return (rng.randint(dmin, 4), rng.randint(0, 4), rng.randint(0, 3))


def gen_in_W(u, minlen=0, maxlen=5, dmin=0):
    """`X ∈ W u` の**使える必要条件だけ**を満たす乱択列: `X=[]` か `lev X 0 <= u`。"""
    X = [rnd_col(dmin) for _ in range(rng.randint(minlen, maxlen))]
    if not X:
        return X
    for _ in range(80):
        if lev(X[0]) <= u:
            return X
        X[0] = (X[0][0], rng.randint(0, u // 2), rng.randint(0, min(3, u)))
    return None


# ---- 構造的に鳴りえない結論の形 ----
SHAPE = {
    'CoreSingleton': ('∈ GX', 'GX の結論の根は (0,v+t,z)、lev = 2(v+t)+z <= a は前提'),
    'CoreCtxSuffixLift': ('∈ GX', '同上'),
    'CorePlantCtxLift': ('∈ GX', '同上'),
    'GraftFromExp': ('∈ Wstar', 'Wstar の結論の根は (0,v,z)、lev = 2v+z <= a は前提'),
    'Subst1gReviveSelf': ('∈ Wself', 'Wself = M ∈ W (lev M 0)。lev M0 <= lev M0 は自明'),
}

CASES = {}


def case(name, note):
    def deco(f):
        CASES[name] = (f, note)
        return f
    return deco


@case('CoreCap / GraftAll', '根 (0,v+t,z)、lev = 2(v+t)+z <= a は前提そのもの')
def _(off):
    v, z, t = rng.randint(0, 4), rng.randint(0, 1), rng.randint(0, 4)
    a = 2 * (v + t) + z + rng.randint(0, 4)
    M = [rnd_col(1) for _ in range(rng.randint(1, 4))]
    return ([(0, v + t, z)] + M[:-1] + [(M[-1][0], rng.randint(0, 5), rng.randint(0, 3))],
            a - off)


@case('TowerOK / OK1 / OK2 / TowerGraft2 / TowerExp / Exp2 / Exp2Low',
      '結論は ((0,v,z)::R)⟦n⟧。oper は第 1 列を落とさない ⟹ 根 (0,v,z)、2v+z <= a は前提')
def _(off):
    v, z = rng.randint(0, 4), rng.randint(0, 1)
    a = 2 * v + z + rng.randint(0, 4)
    return ([(0, v, z)] + [rnd_col(1) for _ in range(rng.randint(1, 4))], a - off)


@case('TowerExp2Root', '結論の段は 2v+z ちょうど。根 (0,v,z) の lev = 2v+z で等号')
def _(off):
    v, z = rng.randint(0, 4), rng.randint(0, 1)
    return ([(0, v, z)] + [rnd_col(1) for _ in range(rng.randint(1, 4))],
            2 * v + z - off)


@case('Row0Free', '行 1・行 2 が同じ ⟹ lev M\' 0 = lev M 0 <= a')
def _(off):
    a = rng.randint(0, 12)
    M = gen_in_W(a, 1, 5)
    if M is None:
        return None
    return ([(rng.randint(0, 4), c[1], c[2]) for c in M], a - off)


@case('WCat  A ++ B', '根は A[0]（A=[] なら B[0]）。どちらも lev <= u')
def _(off):
    u = rng.randint(0, 12)
    A, B = gen_in_W(u), gen_in_W(u)
    if A is None or B is None:
        return None
    return (A + B, u - off)


@case('WSnoc  C ++ [p]', '根は C[0]。C ∈ W u より lev <= u')
def _(off):
    u = rng.randint(0, 12)
    C = gen_in_W(u, 1, 5)
    if C is None:
        return None
    return (C + [rnd_col()], u - off)


@case('Subst1 / Subst1g / Subst1gRevive',
      'p>=1 なら根は S[0]（lev <= u）。p=0 なら根は C[0]、C ∈ W (lev S 0) が押さえる')
def _(off):
    u = rng.randint(0, 12)
    S = gen_in_W(u, 1, 5)
    if S is None:
        return None
    p = rng.randint(0, len(S) - 1)
    C = gen_in_W(lev(S[p]), 1, 4)
    if C is None:
        return None
    C = [(S[p][0], C[0][1], C[0][2])] + C[1:]      # entry C 0 0 = entry S 0 p
    return (S[:p] + C + S[p + 1:], u - off)


@case('SubstClosed  flatMap B',
      '根は (B 0)[0]。前提 ∀i, entry (B k) i 0 = entry Q i k で Q[0] に等しい')
def _(off):
    u = rng.randint(0, 12)
    Q = gen_in_W(u, 1, 4)
    if Q is None:
        return None
    out = []
    for k in range(len(Q)):
        B = [Q[k]] + [rnd_col() for _ in range(rng.randint(0, 3))]
        out += B
    return (out, u - off)


@case('ShiftTowerClosedS  shTower Q e n', '根は k=0 の写しの Q[0]（ずれ 0）')
def _(off):
    u, e, n = rng.randint(0, 12), rng.randint(0, 4), rng.randint(1, 4)
    Q = gen_in_W(u, 1, 4)
    if Q is None:
        return None
    out = []
    for k in range(n):
        out += [(c[0] + k * e, c[1], c[2]) for c in Q]
    return (out, u - off)


@case('LiftStage  Lift1 X d', '根は錐に反射で入る ⟹ lev +2d、段も +2d')
def _(off):
    m, d = rng.randint(0, 12), rng.randint(0, 4)
    X = gen_in_W(m, 1, 5)
    if X is None:
        return None
    return ([(X[0][0], X[0][1] + d, X[0][2])] + X[1:], m + 2 * d - off)


@case('LiftStageParented  (Lift1 X d)⟦n⟧',
      'oper は第 1 列を落とさない ⟹ 根は Lift1 X d の根。前提の Lift1 (X⟦n⟧) d と同じ根')
def _(off):
    m, d = rng.randint(0, 12), rng.randint(0, 4)
    X = gen_in_W(m, 2, 5)
    if X is None or len(X) < 2:
        return None
    return ([(X[0][0], X[0][1] + d, X[0][2])] + X[1:], m + 2 * d - off)


@case('LiftTie  Lift1 ((0,v,z)::R) d', '根 (0,v+d,z)、lev = 2v+z+2d <= m+2d')
def _(off):
    m, d = rng.randint(0, 12), rng.randint(0, 4)
    v, z = rng.randint(0, 4), rng.randint(0, 1)
    if 2 * v + z > m:
        return None
    return ([(0, v + d, z)] + [rnd_col(1) for _ in range(rng.randint(1, 4))],
            m + 2 * d - off)


@case('LiftTieSelf  段を 2v+z に固定', '根 (0,v+d,z)、lev = 2v+z+2d ＝ 段と**等号**')
def _(off):
    d, v, z = rng.randint(0, 4), rng.randint(0, 4), rng.randint(0, 1)
    return ([(0, v + d, z)] + [rnd_col(1) for _ in range(rng.randint(1, 4))],
            2 * v + z + 2 * d - off)


@case('MliftR  mliftR X w d', 'coneVR X w 0 は coneVR_zero（緑）で**常に真** ⟹ 根は必ず +d')
def _(off):
    m, d, w = rng.randint(0, 12), rng.randint(0, 4), rng.randint(0, 4)
    X = gen_in_W(m, 1, 5)
    if X is None:
        return None
    return ([(X[0][0], X[0][1] + d, X[0][2])] + X[1:], m + 2 * d - off)


@case('Row1Mono  行 1 を下げる', 'lev は減る')
def _(off):
    a = rng.randint(0, 12)
    M = gen_in_W(a, 1, 5)
    if M is None:
        return None
    return ([(c[0], rng.randint(0, c[1]), c[2]) for c in M], a - off)


@case('WConvex  Le1 A B, Le1 B C', 'Le1 B C と C ∈ W a から lev B0 <= lev C0 <= a')
def _(off):
    a = rng.randint(0, 12)
    C = gen_in_W(a, 1, 5)
    if C is None:
        return None
    return ([(c[0], rng.randint(0, c[1]), c[2]) for c in C], a - off)


@case('Row1DownLocal  Lift1 X d',
      '前提 mlift X (entry X 1 0 - 1) d ∈ W a。coneV は根で真（1<=entry X 1 0）⟹ 同じ根')
def _(off):
    a, d = rng.randint(0, 12), rng.randint(0, 4)
    X = [rnd_col() for _ in range(rng.randint(1, 5))]
    X[0] = (X[0][0], rng.randint(1, 4), X[0][2])          # 1 <= entry X 1 0
    root = (X[0][0], X[0][1] + d, X[0][2])
    if lev(root) > a:
        return None                                        # 前提 mlift … ∈ W a に反する
    return ([root] + X[1:], a - off)


@case('Row1DownRoot0  Lift1 X d',
      '前提 shiftr01 0 d X ∈ W a。entry X 1 0 = 0 なので両方の根が (·, d, ·)')
def _(off):
    a, d = rng.randint(0, 12), rng.randint(0, 4)
    X = [rnd_col() for _ in range(rng.randint(1, 5))]
    X[0] = (X[0][0], 0, X[0][2])                           # entry X 1 0 = 0
    root = (X[0][0], d, X[0][2])
    if lev(root) > a:
        return None
    return ([root] + X[1:], a - off)


N = 200000
print('### R95 全核版: 反証器が鳴りうるか（結論の根の lev が前提から段以下になるか）')
print()
print('## A. 結論の形から**構造的に**鳴りえないもの（測定不要）')
for k, (shape, why) in SHAPE.items():
    print(f'  {k:22s} 結論 {shape:10s} … {why}')
print()
print(f'## B. 乱択で確かめたもの（各 {N} 件。前提の根の条件だけを満たす**上位集合**）')
print(f'  {"核":58s} {"本物":>8s} {"対照(段-1)":>12s}  判定')
tot_fire = 0
for name, (f, note) in CASES.items():
    row = []
    for off in (0, 1):
        fire = 0
        for _ in range(N):
            r = f(off)
            if r is None:
                continue
            Y, u = r
            if Y and lev(Y[0]) > u:
                fire += 1
        row.append(fire)
    tot_fire += row[0]
    mark = '**射程内**' if row[0] > 0 else '鳴りえない'
    print(f'  {name:58s} {row[0]:8d} {row[1]:12d}  {mark}')
    print(f'      {note}')
print()
print(f'★ **鳴りうる核: {tot_fire and "あり" or "0 本"}**'
      + ('' if tot_fire else ' ⟹ 反証のプログラム全体を閉じてよい'))
