# -*- coding: utf-8 -*-
"""**課題 (z3) —— `j = 0` ∧ `p_rel = 0` のとき `V` は `Q` のずらし／リフトか。**

## 前提の逐語（教訓 2）

`L105Cap:4177`  `mTower Q d0 d1 n = (List.range n).flatMap fun k =>
                     Lift1 (shiftr01 (d0*k) 0 Q) (d1*k)`
`Wset:927`      `Lift1 X d = (range |X|).map fun i =>
                     (entry X 0 i, entry X 1 i + (if le1 X 0 i then d else 0), entry X 2 i)`
`Wset:1320`     `W_shift : M ∈ W u → shiftr01 d 0 M ∈ W u`  （緑）

## ★ 予想を先に書く（教訓 45）＋ 見積もり

`|Lift1 X t| = |X|`、`|shiftr01 d 0 Q| = |Q|` なので**塔のブロックはどれも長さ `|Q|`**。
`p_rel = 0` ⟹ `par = (n-1)*|Q|`、`last = n*|Q|` ⟹ `V = S[(n-1)|Q| : n|Q|]`
                                              **＝ 塔の第 `n-1` ブロックそのもの**

> **⚠ (z3a) `V = Lift1 (shiftr01 (d*(n-1)) 0 Q) (e*(n-1))` は **100%**（定義から出るはず）。**
> **⚠ ただし「純粋なずらし」`V = shiftr01 δ 0 Q` になるのは `e*(n-1)` のリフトが効かないときだけ。
>   見積もり **30〜50%**（`e = 0` が 25%、＋ `le1 Q 0 i` がどこでも偽の場合）。**
> **⚠ 反例の形: 親が第 `n-1` ブロックより手前にあると `|V| > |Q|` になり、この話は崩れる。
>   そこも数える（§R130 の「復活先は必ず直前のブロック」の再確認）。**

**箱**: `|Q| = 3,4,5,6`、値域 < 4 と < 6、`n ∈ 2..5`、`(d,e) ∈ 0..3` / `0..5`。
**単位**: `j = 0` の段 1 つ。**`W` 所属は判定しない。**
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower, Lift1, sh
from r141 import block


def run(E, LS, NS, DE, nsamp, seed):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    prel = {L: Counter() for L in LS}
    for _ in range(nsamp):
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e, n = rnd.choice(DE), rnd.choice(DE), rnd.choice(NS)
        T = [tuple(x) for x in mTower(Q, d, e, n)]
        S = T + block(Q, d, e, n)[:1]          # ← j = 0
        last = len(S) - 1
        par = trio.parent(S, srow(S, last), last)
        if par is None: continue
        c['母集団 (j=0 で親あり)'] += 1
        blk, pr = divmod(par, L)               # 親のブロック番号とブロック内位置
        c[('親のブロック', n - 1 - blk)] += 1   # 0 = 直前のブロック
        if blk != n - 1:
            c['⚠ 親が直前のブロックでない'] += 1
            continue
        prel[L][pr] += 1
        if pr != 0:
            c['p_rel >= 1 （|V| < |Q|、減る）'] += 1
            continue
        c['★ p_rel = 0 （|V| = |Q|、減らない）'] += 1
        V = [tuple(x) for x in S[par:last]]
        # (z3a) 塔の第 n-1 ブロックそのものか
        want = [tuple(x) for x in Lift1(sh(Q, d * (n - 1)), e * (n - 1))]
        if V == want: c["  (z3a) ★ V = Lift1 (shiftr01 (d*(n-1)) 0 Q) (e*(n-1))"] += 1
        else:
            c['  ⚠ (z3a) 一致しない'] += 1
            if len(ex) < 3: ex.append(('a', Q, d, e, n, V, want))
        # 純粋なずらしか（`W_shift` がそのまま効く形）
        dl = V[0][0] - Q[0][0]
        pure = [(p[0] + dl, p[1], p[2]) for p in Q]
        if V == pure: c['  (z3a) V = shiftr01 δ 0 Q（純粋なずらし。W_shift が直に効く）'] += 1
        elif V == want: c["  (z3a) ⚠ リフトが効いている（W_shift だけでは足りない）"] += 1
        if e * (n - 1) == 0: c['     うち e*(n-1) = 0'] += 1
    t = c['母集団 (j=0 で親あり)']
    print(f'### 値域<{E} |Q|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)}  母集団 {t}  [{time.time()-t0:.1f}s]')
    print('    親のブロック（0=直前、1=2つ前…）: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    for k in ['⚠ 親が直前のブロックでない', 'p_rel >= 1 （|V| < |Q|、減る）',
              '★ p_rel = 0 （|V| = |Q|、減らない）']:
        print(f'    {k:38s} {c[k]:7d} ({100*c[k]/max(t,1):6.2f}%)')
    p0 = c['★ p_rel = 0 （|V| = |Q|、減らない）']
    for k in sorted(x for x in c if isinstance(x, str)):
        if k.startswith('  '):
            print(f'    {k:64s} {c[k]:7d} / {p0} ({100*c[k]/max(p0,1):6.2f}%)')
    print('    (z3c) `p_rel` の分布（|Q| ごと）:')
    for L in LS:
        s = sum(prel[L].values())
        if s: print(f'        |Q|={L}: ' + ' '.join(
            f'{k}:{100*prel[L][k]/s:.1f}%' for k in sorted(prel[L])) + f'   (n={s})')
    for x in ex: print('      ⚠ 不一致例', x[1:5], 'V=', x[5], 'want=', x[6])
    print()


if __name__ == '__main__':
    run(4, (3, 4, 5, 6), (2, 3, 4), range(4), 60000, 91)
    print('#### 教訓 21: 箱を広げる')
    run(6, (3, 4, 5, 6, 8), (2, 3, 4, 5), range(6), 60000, 93)
