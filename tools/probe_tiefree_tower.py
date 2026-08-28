"""課題 L11: `(WL)` が **本当に消費される場所** だけで `TieFree` を測る。

`Wtower2.towerGraft2_of_liftStage` を読むと `LiftStage` (= (WL)) は**ただ 1 行**
でしか使われていない:

    have hmem : Lift1 (M⟦j⟧) d1 ∈ W (2*v+z+2*d1) := hWL _ _ _ ih

ここで `M = (0,v,z) :: R`、`d1 = row1(R[-1]) - v`、そして

    M⟦0⟧   = []
    M⟦j+1⟧ = (0,v,z) :: graft R (Lift1 (M⟦j⟧) d1)          (`hstep`)

つまり `(WL)` に要るのは**すべての `X ∈ W m`** ではなく、この**塔の族**だけ。
（Lean 側の切り出し: `Wtower2.LiftStageTower`。）

課題 L10 の測定は `cons` を `∀ v` で盲目に走らせて 50% 破れたが、塔では
`v` は塔のデータで固定され、`cons` の相手も `graft R (Lift1 · d1)` に固定
されている。**量詞が違う。** そこで測るのは:

  (A) 塔の 1 段は `TieFree` を保つか（`TieFree(X_1) ⟺ TieFree(X_j)` か）
  (B) 土台 `TieFree ((0,v,z) :: R.dropLast)` はどれくらい成り立つか
  (C) 陽性対照: リフト量を `d1 ± 1` にすると保存が壊れるか
  (D) 陽性対照: tower-2 の絞りを外すと破れるか

結果（`python3 probe_tiefree_tower.py 3 5 5 5`）:

    tower-2 サイト（v>=1）26412
      土台 TieFree            18772 / **破れ 7640（29%）**
      土台 OK -> 全段 OK      18772 / **後で破れる 0**
      土台 NG -> 全段 NG       7640 / **途中で直る 0**
      陽性対照 d1-1            2398 中 **1604 で後から破れる**
      陽性対照 絞り外し        4422 中 **1080 破れ**（maxlen=2）

⟹ 塔の 1 段は `TieFree` を**完全に保つ**。残るのは土台だけ。ところが土台は
29% で偽で、`X_1 ∈ W (2v+z)` を課しても消えない（`crosstab` を見よ）。
`TowerGraft2` が `∀ v z` を走る以上、`v` は `R` の行 1 の値を必ず走るからで
ある（タイの 1284/1364 は「`R` の中に行 1 がちょうど `v` の列がある」形）。
"""
import sys
import itertools
from collections import Counter

sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio

NS = (1, 2)
MAXD = 11
MAXLEN_W = 44


def lev(c):
    return 2 * c[1] + c[2]


def srow(c):
    return 2 if c[2] > 0 else (1 if c[1] > 0 else 0)


def cone(X):
    """{ j | le1 X 0 j } — 根の行 1 錐（`Lift1` のマスク）。"""
    return {i for i in range(len(X)) if trio.is_ancestor(X, 1, 0, i)}


def Lift1(X, t):
    C = cone(X)
    return [(c[0], c[1] + (t if i in C else 0), c[2]) for i, c in enumerate(X)]


def graft(M, y):
    w = M[-1][0]
    return M[:-1] + [(p[0] + w, p[1], p[2]) for p in y]


def anc0(S, j):
    out, x = [], j
    while x is not None:
        out.append(x)
        x = trio.parent(S, 0, x)
    return out


def amin(S, j):
    return min(S[y][1] for y in anc0(S, j))


def tiefree(X):
    """`coneV(v0-1)` 錐 ⊆ `le1` 錐。逆包含は無条件（`Wtower2.coneV_of_le1`）。"""
    v0 = X[0][1]
    c1 = cone(X)
    c2 = {j for j in range(len(X)) if amin(X, j) >= v0}
    assert c1 <= c2, ('coneV_of_le1 が破れた', X)
    return c2 <= c1


def window(X):
    """`liftStage_of_window` の仮定: 根が行 0 でも行 1 でも狭義最小。"""
    return (all(X[l][0] > X[0][0] for l in range(1, len(X)))
            and all(X[l][1] > X[0][1] for l in range(1, len(X))))


def inW(S, a, d, memo):
    """`W a` の部分決定手続き（`probe_row1mono.py` と同じ。`snoc_zeroRow2` 込み）。"""
    S = tuple(tuple(c) for c in S)
    key = (S, a)
    if key in memo:
        return memo[key]
    if len(S) == 0:
        return True
    if len(S) == 1:
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if all(c[2] == 0 for c in S[:-1]):
        r = lev(S[0]) <= a
        memo[key] = r
        return r
    if d <= 0 or len(S) > MAXLEN_W:
        return None
    memo[key] = None
    out = True
    for n in NS:
        r = inW(trio.expand(list(S), n), a, d - 1, memo)
        if r is False:
            memo[key] = False
            return False
        if r is None:
            out = None
    memo[key] = out
    return out


def branch(M):
    R = M[1:]
    L = len(R)
    if L == 0:
        return 'nil'
    if L <= 1 and lev(R[0]) == 0:
        return 'B1'
    if trio.parent(R, srow(R[-1]), L - 1) is not None:
        return 'B2a'
    if lev(R[-1]) == 0:
        return 'B2b-succ'
    p = trio.parent(M, srow(R[-1]), L)
    if p == 0:
        return 'B3-tower' + str(srow(R[-1]))
    if p is not None:
        return 'B3-revive-nonroot'
    return 'B3-dead'


def family(v, z, R, d1, J):
    """`X_0 = []`, `X_{j+1} = (0,v,z) :: graft R (Lift1 X_j d1)`。"""
    out, X = [[]], []
    for _ in range(J):
        X = [(0, v, z)] + graft(R, Lift1(X, d1))
        out.append(X)
    return out


def sites(maxlen, r0, r1):
    cols = [(a, b, c) for a in range(1, r0) for b in range(r1)
            for c in range(2)]
    for k in range(1, maxlen + 1):
        for R in itertools.product(cols, repeat=k):
            R = list(R)
            for v in range(r1):
                for z in range(2):
                    yield v, z, R


def run(maxlen, r0, r1, J):
    st = Counter()
    ctrl = Counter()
    memo = {}
    ex = {}
    for v, z, R in sites(maxlen, r0, r1):
        M = [(0, v, z)] + R
        b = branch(M)
        if b != 'B3-tower2':
            # (D) 陽性対照: 絞りを外した (v,z,R) で同じ族を作る
            if v >= 1:
                d1c = max(1, R[-1][1] - v)
                fam = family(v, z, R, d1c, min(J, 3))
                ctrl['ext-tot'] += 1
                ctrl['ext-ok' if all(tiefree(X) for X in fam[1:])
                     else 'ext-BAD'] += 1
            continue
        if v < 1:
            st['v0'] += 1
            continue
        d1 = R[-1][1] - v
        assert d1 >= 1
        st['sites'] += 1
        fam = family(v, z, R, d1, J)
        tf = [tiefree(X) for X in fam[1:]]
        st['base' if tf[0] else 'NObase'] += 1
        if tf[0]:
            st['keep' if all(tf) else 'BREAKlater'] += 1
        else:
            st['allbad' if not any(tf) else 'mixed'] += 1
            w = inW(fam[1], 2 * v + z, MAXD, memo)
            st['tieButInW' if w is True else 'tie-notW-or-undec'] += 1
            if w is True and 'tieW' not in ex:
                ex['tieW'] = (v, z, R, d1, fam[1])
            ties = [j for j in range(len(fam[1]))
                    if amin(fam[1], j) >= v and j not in cone(fam[1])]
            st['tie-row1-eq-v' if all(fam[1][j][1] == v for j in ties)
               else 'tie-row1-gt-v'] += 1
        st['window' if all(window(X) for X in fam[1:]) else 'NOwindow'] += 1
        # (C) 陽性対照: リフト量をずらす
        for ds, tag in ((-1, 'd-1'), (1, 'd+1')):
            if d1 + ds < 0:
                continue
            f2 = family(v, z, R, d1 + ds, J)
            t2 = [tiefree(X) for X in f2[1:]]
            if t2[0]:
                ctrl[tag + '-tot'] += 1
                ctrl[tag + '-BAD' if not all(t2) else tag + '-ok'] += 1
    print(f"== 塔 tower-2 サイト: maxlen={maxlen} r0={r0} r1={r1} J={J}")
    print(f"  v>=1 のサイト {st['sites']}   (v=0 は {st['v0']} 個: `TieFree` は空虚)")
    print(f"  [B] 土台 TieFree((0,v,z)::R.dropLast) : {st['base']} "
          f"/ **破れ {st['NObase']}**")
    print(f"  [A] 土台 OK -> 全段 OK : {st['keep']} / **後で破れる {st['BREAKlater']}**")
    print(f"      土台 NG -> 全段 NG : {st['allbad']} / **途中で直る {st['mixed']}**")
    print(f"  参考 窓(liftStage_of_window) : {st['window']} / 破れ {st['NOwindow']}")
    print(f"  破れのうち X_1 ∈ W(2v+z) : {st['tieButInW']} "
          f"(W 外 or 未判定 {st['tie-notW-or-undec']})")
    print(f"  破れのタイは行 1 がちょうど v : {st['tie-row1-eq-v']} "
          f"/ v より上 {st['tie-row1-gt-v']}")
    print(f"  [C] 陽性対照 d1-1 : {ctrl['d-1-ok']} 保つ / **{ctrl['d-1-BAD']} 破れ** "
          f"/ {ctrl['d-1-tot']}")
    print(f"      陽性対照 d1+1 : {ctrl['d+1-ok']} 保つ / {ctrl['d+1-BAD']} 破れ "
          f"/ {ctrl['d+1-tot']}")
    print(f"  [D] 陽性対照 絞り外し : {ctrl['ext-ok']} 保つ / **{ctrl['ext-BAD']} 破れ** "
          f"/ {ctrl['ext-tot']}")
    if 'tieW' in ex:
        v, z, R, d1, X = ex['tieW']
        print(f"  反例（W に入るのにタイ）: v={v} z={z} R={R} d1={d1} X_1={X}")


if __name__ == '__main__':
    ml = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    r0 = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    r1 = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    J = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    run(ml, r0, r1, J)
