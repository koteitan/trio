# -*- coding: utf-8 -*-
"""**R95 —— 核ごとに「反証器が鳴りうるか」を機械的に判定する。**

R94 の定理: 健全な反証器が鳴る **⟺ `lev S 0 > a`**。
⟹ 核「仮定 ⟹ 結論 `Y ∈ W u`」が反証されうる **⟺ 仮定から `lev Y 0 <= u` が出ないこと**。

仮定から使える必要条件は 1 本だけ（`Wset.lean:2161` `lev_root_le_of_mem_W`、無条件・緑）:

    `X ∈ W m` かつ `X ≠ []`  ⟹  `lev X 0 <= m`

そこで各核について、**仮定の根の条件だけを満たす乱択データ**を作り、
結論の根の条件 `lev Y 0 <= u` が破れることがあるかを数える。

  破れが出る  ⟹ その核は反証器の射程内。**H12 はそこに予算を寄せるべき**
  破れが出ない ⟹ その核は**原理的に反証不能**。「違反 0」は情報を持たない

陽性対照: 同じ核の**段を 1 下げた偽物**（結論の段を `u-1` にする）。必ず鳴るはず。
"""
import random
from collections import Counter

rng = random.Random(20260830)


def lev(c):
    return 2 * c[1] + c[2]


def rnd_seq(minlen=0, maxlen=5):
    return [(rng.randint(0, 4), rng.randint(0, 4), rng.randint(0, 3))
            for _ in range(rng.randint(minlen, maxlen))]


def gen_in_W(u, minlen=0, maxlen=5):
    """`X ∈ W u` から**使える必要条件だけ**を満たす乱択列: `X = []` か `lev X 0 <= u`。"""
    X = rnd_seq(minlen, maxlen)
    if not X:
        return X
    # 根の lev を u 以下に押し込む
    for _ in range(60):
        if lev(X[0]) <= u:
            return X
        X[0] = (X[0][0], rng.randint(0, u // 2), rng.randint(0, min(3, u)))
    return None


CASES = {}


def case(name):
    def deco(f):
        CASES[name] = f
        return f
    return deco


@case('WCat  A ++ B')
def _(off):
    u = rng.randint(0, 12)
    A, B = gen_in_W(u), gen_in_W(u)
    if A is None or B is None:
        return None
    Y = A + B
    return (Y, u - off)


@case('WSnoc  C ++ [p]')
def _(off):
    u = rng.randint(0, 12)
    C = gen_in_W(u, 1, 5)
    if C is None:
        return None
    Y = C + [(rng.randint(0, 4), rng.randint(0, 4), rng.randint(0, 3))]
    return (Y, u - off)


@case('LiftStage  Lift1 X d')
def _(off):
    m, d = rng.randint(0, 12), rng.randint(0, 4)
    X = gen_in_W(m, 1, 5)
    if X is None:
        return None
    Y = [(X[0][0], X[0][1] + d, X[0][2])] + X[1:]   # 根は必ず錐に入る（反射）
    return (Y, m + 2 * d - off)


@case('LiftTie  Lift1 ((0,v,z)::R) d')
def _(off):
    m, d = rng.randint(0, 12), rng.randint(0, 4)
    v, z = rng.randint(0, 4), rng.randint(0, 1)
    if 2 * v + z > m:
        return None                                   # 仮定 (0,v,z)::R ∈ W m に反する
    R = rnd_seq(1, 4)
    Y = [(0, v + d, z)] + R
    return (Y, m + 2 * d - off)


@case('MliftR  mliftR X w d')
def _(off):
    m, d, w = rng.randint(0, 12), rng.randint(0, 4), rng.randint(0, 4)
    X = gen_in_W(m, 1, 5)
    if X is None:
        return None
    r = X[0]
    Y = [(r[0], r[1] + (d if r[1] > w else 0), r[2])] + X[1:]
    return (Y, m + 2 * d - off)


@case('Row1Mono  M -> M1 (行 1 を下げる)')
def _(off):
    a = rng.randint(0, 12)
    M = gen_in_W(a, 1, 5)
    if M is None:
        return None
    Y = [(c[0], rng.randint(0, c[1]), c[2]) for c in M]
    return (Y, a - off)


@case('WConvex  Le1 A B, Le1 B C')
def _(off):
    a = rng.randint(0, 12)
    C = gen_in_W(a, 1, 5)
    if C is None:
        return None
    Y = [(c[0], rng.randint(0, c[1]), c[2]) for c in C]   # B は C 以下（Le1）
    return (Y, a - off)


@case('CoreCap  Lift1 ((0,v,z)::cap M b c) t')
def _(off):
    v, z, t = rng.randint(0, 4), rng.randint(0, 1), rng.randint(0, 4)
    a = 2 * (v + t) + z + rng.randint(0, 4)
    M = [(rng.randint(1, 3), rng.randint(0, 3), rng.randint(0, 3))
         for _ in range(rng.randint(1, 4))]
    Y = [(0, v + t, z)] + M[:-1] + [(M[-1][0], rng.randint(0, 5), rng.randint(0, 3))]
    return (Y, a - off)


@case('TowerOK  (0,v,z) :: (塔)')
def _(off):
    v, z = rng.randint(0, 4), rng.randint(0, 1)
    a = 2 * v + z + rng.randint(0, 4)
    Y = [(0, v, z)] + rnd_seq(1, 4)
    return (Y, a - off)


N = 200000
print(f'### R95 核ごとに反証器が鳴りうるか（各 {N} 件の乱択）')
print(f'{"核":42s} {"本物":>10s} {"陽性対照(段 -1)":>16s}')
for name, f in CASES.items():
    row = []
    for off in (0, 1):
        fire = skip = 0
        for _ in range(N):
            r = f(off)
            if r is None:
                skip += 1
                continue
            Y, u = r
            if not Y:
                continue
            if lev(Y[0]) > u:
                fire += 1
        row.append(fire)
    mark = '**射程内**' if row[0] > 0 else '反証不能'
    print(f'{name:42s} {row[0]:10d} {row[1]:16d}   {mark}')
