# -*- coding: utf-8 -*-
"""**課題 H57-c: `Subst1gRevive` / `Subst1gReviveSelf` / `Subst1g` を測る。**

`WSnoc` と同じく**仮定が全部 `∈ W` / 決定可能な構文条件**なので、
`wref` の反証器だけで閉じる（`Wstar` の ∀ が無い）。

    `Subst1g`          `Wtower2:2720`  … 既存 `tools/probe_subst1g.py`（210201 件・違反 0）
    `Subst1gRevive`    `Wtower2:3251`  … `Subst1g` の**残差**（復活の場合だけ）。**弱い**
    `Subst1gReviveSelf``Wtower2:3274`  … 段の量詞を落とした形（`Wself`）。**もっと弱い**

弱いほうに反例が出れば強いほうも死ぬので、**`Subst1gReviveSelf` から測る**。
（`Subst1g → Subst1gRevive → Subst1gReviveSelf` の向きは `CORES.md` の
「より強いもの」列。`subst1gRevive_of_self` は `Self → Revive`。）

**向き**: 仮定は `inW == True`（過大 ⟹ 認めやすい）、違反は `inW == False`（健全）。
"""
import sys, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/h1')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
import wref
from wref import Ref, fmt, srow, has_parent, has_parent_last, levM, entry
from collections import Counter

AMAX = 12


def subst(S, p, C):
    return list(S[:p]) + list(C) + list(S[p + 1:])


def main(lens=(1, 2), cols=None, ccols=3, tag=''):
    ref = Ref(ns=(1, 2, 3), maxdepth=9, maxlen=34, maxnodes=6000)
    wref.print_controls(ref)
    if cols is None:
        cols = [(a, b, c) for a in range(3) for b in range(3)
                for c in range(2)]
    Ss = []
    for L in lens:
        for S in itertools.product(cols, repeat=L):
            Ss.append(list(S))
    print('## 母集団%s' % tag)
    print()
    print('宿主 `S`: 長さ %s、列 = 行0<3・行1<3・行2<2 ⟹ **%d** 本'
          % (list(lens), len(Ss)))
    dec = [(S, ref.minstage(S, AMAX)) for S in Ss]
    dec = [(S, u) for S, u in dec if u is not None]
    print('うち段が確定したもの: **%d**' % len(dec))
    print()

    tot = Counter()
    totself = Counter()
    ctl = Counter()
    ex, exs = [], []
    rows = []
    for S, u in dec:
        for p in range(len(S)):
            d = entry(S, 0, p)
            lsp = levM(S, p)
            D = S[p + 1:]
            # ---- ブロック C の候補: 頭が深さ d、他は d 以上（非狭義）
            heads = [(d, b, c) for b in range(ccols) for c in range(2)]
            tails = [(e, b, c) for e in range(d, d + ccols)
                     for b in range(ccols) for c in range(2)]
            Cs = [[h] for h in heads]
            Cs += [[h, t] for h in heads for t in tails]
            for C in Cs:
                inw = ref.inW(C, lsp)
                R = subst(S, p, C)
                if len(R) > 6:
                    continue
                # ---- 復活の側条件（決定可能）
                if not has_parent_last(R):
                    tot['末尾に親が無い（仮定を満たさない）'] += 1
                    continue
                disj = ((not D and not has_parent_last(C)) or
                        (D and not has_parent_last(D)))
                if not disj:
                    tot['場合分けの選言が偽（仮定を満たさない）'] += 1
                    continue
                if inw is not True:
                    # 陰性対照: `C ∈ W (lev S p)` を落とした版
                    if inw is False:
                        r = ref.inW(R, u)
                        ctl['**違反**' if r is False
                            else 'OK' if r is True else '未判定'] += 1
                    else:
                        tot['`C ∈ W (lev S p)` が未判定'] += 1
                    continue
                # ---- Subst1gRevive
                r = ref.inW(R, u)
                k = '**違反**' if r is False else 'OK' if r is True else '未判定'
                tot[k] += 1
                rows.append((k, R))
                if r is False and len(ex) < 8:
                    ex.append((S, p, C, u))
                # ---- Subst1gReviveSelf（段の量詞を落とした形）
                if levM(C, 0) <= lsp and any(q[2] > 0 for q in R[:-1]):
                    rs = ref.inW(R, levM(R, 0))
                    ks = ('**違反**' if rs is False
                          else 'OK' if rs is True else '未判定')
                    totself[ks] += 1
                    if rs is False and len(exs) < 8:
                        exs.append((S, p, C))
    print('**`Subst1gRevive`（復活の残差。`u = minstage S`）**')
    print()
    wref.tally(tot, '結果')
    for S, p, C, u in ex:
        print('    反例: S=`%s` p=%d C=`%s` u=%d ⟹ R=`%s`'
              % (fmt(S), p, fmt(C), u, fmt(subst(S, p, C))))
    if ex:
        print()
    wref.tally(totself, '`Subst1gReviveSelf`（`Wself` 形、行 2 が正の列が dropLast にある場合）')
    for S, p, C in exs:
        print('    反例: S=`%s` p=%d C=`%s`' % (fmt(S), p, fmt(C)))
    if exs:
        print()
    wref.tally(ctl, '陰性対照（`C ∈ W (lev S p)` を確定で破る C。違反が出るべき）')
    wref.degeneracy(rows)
    return tot


if __name__ == '__main__':
    main(lens=(1, 2), tag='（長さ 1..2）')
    print()
    main(lens=(3,), tag='（長さ 3 だけ。長さで傾向が変わらないことを見る）')
