# -*- coding: utf-8 -*-
"""**課題 (p5) —— `le0` の祖先を近いブロックへずらしても届くか。**

## 的（team-lead の直した形）

    **`le0 T (m|Q| + x) ((k+1)|Q|)` かつ `m <= k`  ⟹  `le0 T (k|Q| + x) ((k+1)|Q|)`**
    （`T = mTower Q d e n`）

## ★ 先に気づいたこと（検算に入れる）

`mTower Q d e n` のブロック `k` ＝ `Lift1 (shiftr01 (d*k) 0 Q) (e*k)`。
**`Lift1` は行 1 しか変えない**（`Wset:927`、`entry0_Lift1`（`:948`）は行 0 が不変）。
⟹ **塔の行 0 は `e` に依存しない** ⟹ **`le0` も `e` に依存しない**。
⟹ **(p5a) の答えは `e` に依らないはず。** これも測って確かめる（(p5e)）。

## ★ 予想（教訓 45）＋ 見積もり

⚠ **3 回連続で見積もりを外している。前回外した方向を根拠にしない**（自分の教訓）。
機構から素直に:

> **⚠ (p4a) で同じ形を `e = 0` について 147,705 組・違反 0 で測っている。
>   (p5) はその一般化（`m <= k`、`e` 任意）。**
> **⚠ 見積もり **100%**。ただし箱を大きく広げ、陰性対照（`x` を 1 ずらす）を必ず付ける。**
> **⚠ (p5e) `le0` が `e` に依らない … 100%（定義から出るはず）。**

## 規模（先に数える）

`|Q| <= 6`、`n <= 5` ⟹ 塔は最大 30 列。組 `(m, x, k)` は `n * |Q| * n <= 150` /（`Q,d,e,n`）。
`Q` を 3,000 本 × `d,e` 各 1 つ × `n` 4 通り ⟹ **最大 180 万組**。走らせてよい。
"""
import sys, random, time
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r113 import mTower


def le0(T, a, b): return trio.is_ancestor(T, 0, a, b)


def run(E, LS, DS, ES, MS, nsamp, seed, tag):
    rnd = random.Random(seed); c = Counter(); ex = []; t0 = time.time()
    for _ in range(nsamp):
        L = rnd.choice(LS)
        a0 = rnd.randrange(E - 1)
        Q = [(a0, rnd.randrange(E), 0)] + \
            [(rnd.randrange(a0 + 1, E), rnd.randrange(E), rnd.randrange(2))
             for _ in range(L - 1)]
        d = rnd.choice(DS)
        for e in ES:
            key = 'e = 0' if e == 0 else 'e > 0'
            for n in MS:
                T = [tuple(y) for y in mTower(Q, d, e, n)]
                # (p5e) 行 0 が e に依らないか
                T0 = [tuple(y) for y in mTower(Q, d, 0, n)]
                c['(p5e) 塔の組'] += 1
                if [p[0] for p in T] == [p[0] for p in T0]:
                    c['★ (p5e) 行 0 が e に依らない'] += 1
                else:
                    c['⛔ (p5e) 行 0 が e に依る'] += 1
                for k in range(n - 1):
                    tgt = (k + 1) * L
                    for m in range(k + 1):
                        for x in range(L):
                            if not le0(T, m * L + x, tgt): continue
                            c[(key, '★ 分母: le0 (m|Q|+x) 的')] += 1
                            if m == k - 1: c[(key, '  (p5c) 分母 m=k-1')] += 1
                            if le0(T, k * L + x, tgt):
                                c[(key, '★ (p5a) 近いブロックの同じ x も届く')] += 1
                                if m == k - 1: c[(key, '  (p5c) 成立')] += 1
                            else:
                                c[(key, '⛔ (p5a) 破れ')] += 1
                                if len(ex) < 4: ex.append((Q, d, e, n, m, x, k, T))
                            # 陰性対照: x を 1 ずらす
                            xb = (x + 1) % L
                            c[(key, '陰性対照の分母')] += 1
                            if le0(T, k * L + xb, tgt):
                                c[(key, '  ⚠ 1 ずらしても届く')] += 1
                            else:
                                c[(key, '  ★ 1 ずらすと届かない（対照が鳴る）')] += 1
    print(f'### {tag}  [{time.time()-t0:.1f}s]')
    p = c['(p5e) 塔の組']
    print(f'    ★ (p5e) 塔の行 0 が `e` に依らない … {c["★ (p5e) 行 0 が e に依らない"]} / {p} '
          f'({100*c["★ (p5e) 行 0 が e に依らない"]/max(p,1):8.4f}%)')
    for key in ('e = 0', 'e > 0'):
        A = c[(key, '★ 分母: le0 (m|Q|+x) 的')]
        if not A: continue
        cc = c[(key, '  (p5c) 分母 m=k-1')]
        print(f'  {key}   ★ 分母 {A}')
        print(f'      ★ (p5a) 成立            {c[(key,"★ (p5a) 近いブロックの同じ x も届く")]:9d} '
              f'({100*c[(key,"★ (p5a) 近いブロックの同じ x も届く")]/A:8.4f}%)')
        print(f'      ⛔ (p5a) 破れ            {c[(key,"⛔ (p5a) 破れ")]:9d} '
              f'({100*c[(key,"⛔ (p5a) 破れ")]/A:8.4f}%)')
        print(f'      (p5c) m=k-1 だけ         {c[(key,"  (p5c) 成立")]:9d} / {cc} '
              f'({100*c[(key,"  (p5c) 成立")]/max(cc,1):8.4f}%)')
        print(f'      陰性対照 1 ずらすと届かない  {c[(key,"  ★ 1 ずらすと届かない（対照が鳴る）")]:9d} '
              f'({100*c[(key,"  ★ 1 ずらすと届かない（対照が鳴る）")]/A:8.4f}%)  ← 鳴るべき')
    for x in ex:
        print(f'      ⛔ (p5b) 反例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} (m,x,k)=({x[4]},{x[5]},{x[6]})')
        print(f'            塔={x[7]}')
    print()


if __name__ == '__main__':
    run(6,  (2,3,4),   (1,2,3),    (0,1,2,3),   (2,3,4),   3000, 501, '値域<6 |Q|<=4 d<=3 e<=3 n<=4')
    print('#### 教訓 21: 箱を広げる')
    run(12, (3,5,6),   (1,2,4,7),  (0,1,3,6),   (2,3,5),   2000, 503, '★ 値域<12 |Q|<=6 d<=7 e<=6 n<=5')
    run(20, (4,8,12),  (1,3,6,11), (0,2,5,11),  (2,4,6),   800,  505, '★★ 値域<20 |Q|<=12 d<=11 e<=11 n<=6')
