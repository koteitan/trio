# -*- coding: utf-8 -*-
"""**R126 の続き —— 母集団を「`W` 所属が確実に取れた `Q`」に絞る。**

⚠ `MTowerClosedS` / `MTowerOrphan` の前提は **`Q ∈ W u`** である。r126.py の母集団には
それが入っていない。そこで **健全な判定器（`winw.inW2`、True は確実）が True を返した
`Q` だけ**に絞って孤児率を測り直す（§R130 と同じ手）。

**片側性を明記**: `True` は確実、`None`/`False` は捨てる。⟹ この母集団は
**`W` に確実に入る `Q` の部分集合**であって、`W ∩ 箱` そのものではない。
"""
import sys, itertools, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from winw import inW2, lev
from r126 import srow, hasP, classify


def run(cm, L, AS, depth, maxlen):
    COL = [(d, b, c) for d in range(4) for b in range(3) for c in range(cm + 1)]
    memo = {}
    c = Counter(); ex = {}
    t0 = time.time()
    for root in COL:
        tail = [x for x in COL if x[0] > root[0]]
        for t in itertools.product(tail, repeat=L - 1):
            Q = [root] + list(t)
            c['箱の母集団（最浅あり）'] += 1
            cert = None
            for a in AS:
                if inW2(Q, a, depth, memo, maxlen) is True:
                    cert = a
                    break
            if cert is None:
                c['判定できず（捨てる）'] += 1
                continue
            c['★ W 所属が確実'] += 1
            i = srow(Q, L - 1)
            c[('srow', i)] += 1
            if hasP(Q):
                continue
            c['孤児'] += 1
            i, fs = classify(Q)
            c[('孤児srow', i)] += 1
            c[('孤児z', Q[0][2])] += 1
            if not fs:
                c['★★ §79 の形の外'] += 1
                ex.setdefault('外', Q)
            for f in fs:
                c[('形', f)] += 1
                ex.setdefault(f, Q)
            if fs == ['F2b srow=2 行2が根以下']:
                c['⚠ F2b だけ'] += 1
    tot = c['★ W 所属が確実']; orp = c['孤児']
    print(f'  行2<={cm} |Q|={L}  箱 {c["箱の母集団（最浅あり）"]:7d}  '
          f'**W 確実 {tot:7d}**（判定率 {100*tot/max(1,c["箱の母集団（最浅あり）"]):5.1f}%）  '
          f'**孤児 {orp:6d} ({100*orp/max(tot,1):6.2f}%)**  [{time.time()-t0:.1f}s]')
    for i in (0, 1, 2):
        n = c[('srow', i)]; o = c[('孤児srow', i)]
        if n:
            print(f'        srow={i}: 分母 {n:7d}  孤児 {o:6d} ({100*o/n:6.2f}%)'
                  + ('   ⛔ **§79 が偽**' if (i == 0 and o) else ''))
    for z in range(cm + 1):
        print(f'        根の行2 z={z}: 孤児 {c[("孤児z", z)]:6d}')
    for f in sorted(k[1] for k in c if isinstance(k, tuple) and k[0] == '形'):
        print(f'        形 {f:26s} {c[("形", f)]:6d}')
    print(f'        ★★ §79 の形の外 : {c["★★ §79 の形の外"]:6d}'
          + ('  ⛔ **穴**' if c['★★ §79 の形の外'] else '  ✅ **0**'))
    print(f'        ⚠ F2b だけの孤児 : {c["⚠ F2b だけ"]:6d}')
    for k in sorted(ex):
        print(f'        最小例 {k}: {ex[k]}')


if __name__ == '__main__':
    print('### R126w 母集団を「W 所属が確実に取れた Q」に絞る（片側。True のみ採用）')
    for cm in (1, 2):
        for L in (2, 3, 4):
            run(cm, L, range(0, 8), depth=4, maxlen=12)
