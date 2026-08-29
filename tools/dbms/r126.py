# -*- coding: utf-8 -*-
"""**課題 R126（L3 からの直接依頼、SESSION §281）—— 塔のブロックの末尾列が段内で孤児になる割合。**

⚠ **これは `W` 所属ではない。`HasParentInBlock Q` は列だけで決まる述語なので、
私の計器で全数決定できる**（§R94/§R95 の判定）。

**主語**（`L53Subst.lean:914`）:

    `HasParentInBlock N := hasParent N (srow N (N.length - 1)) (N.length - 1)`
    **孤児 ＝ `¬ HasParentInBlock Q`** ＝ 残差 B（`MTowerOrphan`、`L105Cap:6118`）の前提

**§79（`L105Cap:5989-6030`）が主張する形**（教訓 45: 先に写す）:

    `hasParentInBlock_of_srow_zero` : `2<=|Q|` ∧ **根が狭義最浅** ∧ `srow=0` ⟹ 親あり
    `hasParentInBlock_of_srow_one`  : `2<=|Q|` ∧ **根が狭義最浅** ∧ `srow=1`
                                      ∧ `entry Q 1 0 < entry Q 1 (|Q|-1)` ⟹ 親あり
    `hasParentInBlock_of_srow_two`  : `2<=|Q|` ∧ `srow=2`
                                      ∧ `le1 Q 0 (|Q|-1)` ∧ `entry Q 2 0 < entry Q 2 (|Q|-1)` ⟹ 親あり
      （⚠ srow=2 だけ **根が狭義最浅を使っていない**）

⟹ **対偶（孤児が入りうる形）**:

    (F0) `srow = 0`                                        … **起きないはず**（(z3)）
    (F1) `srow = 1` ∧ `entry Q 1 (|Q|-1) <= entry Q 1 0`
    (F2a) `srow = 2` ∧ `¬ le1 Q 0 (|Q|-1)`                 … 「錐の外」
    (F2b) `srow = 2` ∧ `entry Q 2 (|Q|-1) <= entry Q 2 0`  … 「行 2 が根以下」

⚠ **SESSION §281 の (z2) は 2 形（F1 と F2a）しか書いていない。F2b が抜けている。**
   ⟹ **F2b だけに入る孤児を別に数える**（抜けが実際に効くか）。

**箱と単位**:

    単位 … 列 `Q`（塔の 1 ブロック）1 本
    箱  … 行0 ∈ {0..3}, 行1 ∈ {0..2}, 行2 ∈ {0..cm}, `|Q| = L`
    母集団 … `2 <= |Q|` ∧ **根が狭義最浅**（`∀j>=1, entry Q 0 0 < entry Q 0 j`）
    **除外（明記）** … **`Q ∈ W u` は判定しない**（私の計器の決定率 0%。team-lead の常設警告）
    軸 … `L`（3 段以上）× 行2 上限 `cm`（3 段）
"""
import sys, itertools, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter


def srow(S, j):
    return 2 if S[j][2] > 0 else (1 if S[j][1] > 0 else 0)


def hasP(S):
    """`HasParentInBlock S`。"""
    j = len(S) - 1
    return trio.parent(S, srow(S, j), j) is not None


def le1_root(S, j):
    """`le1 S 0 j` ＝ 行 1 の親鎖をたどって 0 に着く（反射も含む）。"""
    return trio.is_ancestor(S, 1, 0, j)


def classify(Q):
    """孤児の形を返す。"""
    j = len(Q) - 1
    i = srow(Q, j)
    fs = []
    if i == 0:
        fs.append('F0 srow=0 **§79 が偽**')
    elif i == 1:
        if Q[j][1] <= Q[0][1]:
            fs.append('F1 srow=1 行1が根以下')
    else:
        if not le1_root(Q, j):
            fs.append('F2a srow=2 錐の外')
        if Q[j][2] <= Q[0][2]:
            fs.append('F2b srow=2 行2が根以下')
    return i, fs


def gen(COL, L, shallow):
    """`|Q| = L` の列を生成。`shallow` なら根が狭義最浅のものだけ。"""
    if not shallow:
        yield from itertools.product(COL, repeat=L)
        return
    for root in COL:
        tail = [c for c in COL if c[0] > root[0]]
        if len(tail) == 0:
            continue
        for t in itertools.product(tail, repeat=L - 1):
            yield (root,) + t


def run(cm, Ls, shallow, label):
    COL = [(d, b, c) for d in range(4) for b in range(3) for c in range(cm + 1)]
    print(f'### {label}  箱 行0<=3 行1<=2 行2<={cm}  根が狭義最浅={"要求" if shallow else "**落とす（陰性対照）**"}')
    for L in Ls:
        c = Counter(); ex = {}
        for Qt in gen(COL, L, shallow):
            Q = list(Qt)
            c['母集団'] += 1
            i = srow(Q, L - 1)
            c[('srow', i)] += 1
            if hasP(Q):
                continue
            c['孤児'] += 1
            i, fs = classify(Q)
            z = Q[0][2]
            c[('孤児srow', i)] += 1
            c[('孤児z', z)] += 1
            if not fs:
                c['★★ §79 の形の外'] += 1
                ex.setdefault('外', Q)
            for f in fs:
                c[('形', f)] += 1
                ex.setdefault(f, Q)
            if fs == ['F2b srow=2 行2が根以下']:
                c['⚠ F2b だけ（§281 の 2 形が取りこぼす）'] += 1
                ex.setdefault('F2bのみ', Q)
        tot = c['母集団']; orp = c['孤児']
        print(f'  |Q|={L}  母集団 {tot:9d}  **孤児 {orp:8d} ({100*orp/max(tot,1):6.3f}%)**')
        for i in (0, 1, 2):
            n = c[('srow', i)]; o = c[('孤児srow', i)]
            if n:
                print(f'      srow={i}: 分母 {n:9d}  孤児 {o:8d} ({100*o/n:6.3f}%)'
                      + ('   ⛔ **§79 が偽**' if (i == 0 and o) else ''))
        for z in range(cm + 1):
            if c[('孤児z', z)] or True:
                print(f'      根の行2 z={z}: 孤児 {c[("孤児z", z)]:8d}')
        for f in sorted(k[1] for k in c if isinstance(k, tuple) and k[0] == '形'):
            print(f'      形 {f:26s} {c[("形", f)]:8d}')
        print(f'      ★★ §79 の形の外 : {c["★★ §79 の形の外"]:8d}'
              + ('  ⛔ **§79 に穴**' if c['★★ §79 の形の外'] else '  ✅ **0（§79 は破れない）**'))
        print(f'      ⚠ F2b だけの孤児 : {c["⚠ F2b だけ（§281 の 2 形が取りこぼす）"]:8d}'
              + ('  ← **§281 の 2 形では足りない**' if c['⚠ F2b だけ（§281 の 2 形が取りこぼす）'] else ''))
        for k in sorted(ex):
            print(f'      最小例 {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    # 見積もり: 本測定 約 183 万件、陰性対照 約 17 万件（L=5 は cm=1 だけ。cm>=2 は 580 万件超なので外す）
    for cm in (1, 2, 3):
        run(cm, (2, 3, 4, 5) if cm == 1 else (2, 3, 4), True,
            'R126 (z1)(z2)(z3) 孤児の割合')
    for cm in (1, 2, 3):
        run(cm, (2, 3), False,
            'R126 陰性対照: 「根が狭義最浅」を落とす')
