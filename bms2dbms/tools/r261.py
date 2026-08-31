# -*- coding: utf-8 -*-
"""**(C4-40) —— L3 の「反例の族」を再構成して C4 を当てる。**

## ⚠ 母集団の作り方（1 行）

`B` の全列挙（長さ 3〜4、行 0 は狭義増加で <= 4、行 1 <= 9、行 2 <= 1、根は `(0,*,0)`）のうち、
**ある窓 `V = B[p:j]`（`|V| >= 2`）で `hlocQ` の行 1 成分が破れる**もの ＝ **反例の族**。
⟹ ★ L3 の `Bce = [(0,0,0),(1,5,0),(2,1,0),(2,9,0)]` と `B = [(0,0,0),(1,2,0),(2,1,0),(3,9,0)]`
   が入ることを**陽性対照**として確認する（教訓 12/23）。
"""
import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r247 import row1_wit
from r257 import C4


def row1_break(B):
    """行 1 成分が破れる窓 `(p, j, t)` を返す。"""
    out = []
    for p in range(len(B) - 1):
        for j in range(p + 2, len(B) + 1):
            V = [tuple(x) for x in B[p:j]]
            for t in range(1, len(V)):
                if V[t][2] != 0 or V[t][1] == 0: continue
                if not row1_wit(V, t): out.append((p, j, t))
    return out


def gen(L, X0, X1, X2):
    for rest in itertools.product(
            [(a, b, c) for a in range(1, X0 + 1) for b in range(X1 + 1)
             for c in range(X2 + 1)], repeat=L - 1):
        B = [(0, 0, 0)] + list(rest)
        if any(B[i][0] > B[i + 1][0] for i in range(len(B) - 1)): continue  # 行0 非減少
        yield B


def main():
    POS = {'L3 Bce': [(0,0,0),(1,5,0),(2,1,0),(2,9,0)],
           'L3 B':   [(0,0,0),(1,2,0),(2,1,0),(3,9,0)],
           'TL 最小': [(0,0,0),(1,1,0),(2,1,0),(2,2,0)]}
    print('## ⚠ 陽性対照（この 3 件が族に入らなければ器具の故障）')
    for nm, B in POS.items():
        br = row1_break(B)
        print(f'   {nm} = {B}: 行1の破れ {len(br)} 件 {br[:3]}   '
              f'C4={"★真" if C4([tuple(x) for x in B]) else "⛔偽"}')
    print()
    for L, X0, X1, X2, tag in ((3, 3, 4, 1, '長さ3 行0<=3 行1<=4'),
                               (4, 3, 4, 1, '長さ4 行0<=3 行1<=4'),
                               (4, 4, 9, 0, '長さ4 行0<=4 行1<=9 行2=0'),
                               (4, 4, 9, 1, '★ 長さ4 行0<=4 行1<=9 行2<=1')):
        c = Counter(); bad = []
        for B in gen(L, X0, X1, X2):
            c['列挙した B'] += 1
            if not row1_break(B): continue
            c['★ 族（行 1 成分が破れる B）'] += 1
            if C4([tuple(x) for x in B]):
                c['⛔ **C4 が真（＝ C4 では殺せない）**'] += 1
                if len(bad) < 6: bad.append(B)
            else:
                c['★ C4 が偽（＝ C4 が殺す）'] += 1
        n = c['★ 族（行 1 成分が破れる B）']
        print(f'### {tag}  列挙 {c["列挙した B"]}  **族 {n}**')
        print(f'    ★ **C4 が偽（殺せる）** {c["★ C4 が偽（＝ C4 が殺す）"]} '
              f'({100*c["★ C4 が偽（＝ C4 が殺す）"]/max(n,1):8.4f}%)   '
              f'⛔ **C4 が真（殺せない）** {c["⛔ **C4 が真（＝ C4 では殺せない）**"]} '
              f'({100*c["⛔ **C4 が真（＝ C4 では殺せない）**"]/max(n,1):8.4f}%)')
        for b in bad:
            print(f'      ⛔ **C4 が真なのに反例**: {b}  破れ {row1_break(b)[:2]}')
        print()


if __name__ == '__main__':
    main()
