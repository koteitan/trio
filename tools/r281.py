# -*- coding: utf-8 -*-
"""**(WIN-DEF) —— 2 つの「越境」の定義を突き合わせる。**

## ⚠ 記法（1 手 `X → Y = oper X n`）

    `x = |X|-1`、`i1 = srow X x`、`r = parent X i1 x`
    **今の悪い部分（＝ 窓）`V = X[r:x]`**、**`|Q| = |V| = x - r`**
    `Y = X[:r] ++ (コピー n 個)`、**最後のブロックの先頭 `bs = r + (n-1)*|Q|`**
    **塔の先頭 `ts = r`**
    `y = |Y|-1`、`i2 = srow Y y`、`r2 = parent Y i2 y`、**次の窓 `V' = Y[r2:y]`**、`|V'| = y - r2`

## 3 つの分類

    **(R2)** `r2 < r`  …… **私の「接頭辞に逃げる手」**（塔より前）
    **(L3-b)** `r2 < bs` … **L3 の「親が最後のブロックの外」**（塔の中でも該当）
    **(L3-t)** `r2 < ts` … 「親が塔の外」＝ **(R2) と同じ**

## 比べるもの

    **`|V'| vs |V|`**（＝ `|V'| vs |Q|`。私の設定では **同一**）
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from trio import expand
from collections import Counter
from r126 import srow
from r263 import load
from r272 import subwins

rng = random.Random(20260830)


def step(X, n):
    x = len(X) - 1
    i1 = srow(X, x)
    r = trio.parent(X, i1, x)
    if r is None: return None
    Q = x - r
    Y = [tuple(v) for v in expand([list(v) for v in X], n)]
    if len(Y) < 2: return None
    bs = r + (n - 1) * Q
    y = len(Y) - 1
    i2 = srow(Y, y)
    r2 = trio.parent(Y, i2, y)
    if r2 is None: return None
    return dict(r=r, Q=Q, Y=Y, bs=bs, y=y, r2=r2, Vp=y - r2, n=n, x=x)


def run(S, NS, DEPTH, tag):
    c = Counter(); ex = []; t0 = time.time()
    for X0 in S:
        for n in NS:
            X = [tuple(v) for v in X0]
            for _ in range(DEPTH):
                s = step(X, n)
                if s is None: break
                R2 = s['r2'] < s['r']
                L3b = s['r2'] < s['bs']
                c['分母'] += 1
                c[f'混同表 (R2={int(R2)}, L3b={int(L3b)})'] += 1
                # |V'| vs |Q|
                k = '減' if s['Vp'] < s['Q'] else ('同' if s['Vp'] == s['Q'] else '増')
                c[f'全体|{k}'] += 1
                c[f'[R2={int(R2)}]|{k}'] += 1
                c[f'[L3b={int(L3b)}]|{k}'] += 1
                if L3b: c[f'[L3b 越境] |V*| < |Q| ? {s["Vp"] < s["Q"]}'] += 1
                if R2 and s['Vp'] >= s['Q'] and len(ex) < 4:
                    ex.append((X, n, s['r'], s['Q'], s['r2'], s['Vp'], s['bs']))
                X = s['Y']
    d = c['分母']
    def pc(x): return f'{x} ({100*x/max(d,1):8.4f}%)'
    print(f'### {tag}  [{time.time()-t0:.1f}s]  分母 {d}')
    print('  ★★ **混同表**（行: 私の R2、列: L3 の L3b）')
    for a in (0, 1):
        print('      R2=%d : ' % a + '  '.join(
            'L3b=%d %s' % (b, pc(c[f'混同表 (R2={a}, L3b={b})'])) for b in (0, 1)))
    print('  ★★ **|V\'| と |Q| の比較**')
    for g, lab in (('全体', '全体'), ('[R2=1]', '⛔ 私の越境（r2<r）'),
                   ('[R2=0]', '★ 私の非越境'), ('[L3b=1]', '⛔ L3 の越境（r2<bs）'),
                   ('[L3b=0]', '★ L3 の非越境')):
        dd = sum(c[f'{g}|{k}'] for k in ('減', '同', '増'))
        print(f'      {lab:22s} 分母 {dd:7d}  減 {100*c[f"{g}|減"]/max(dd,1):7.3f}%  '
              f'同 {100*c[f"{g}|同"]/max(dd,1):7.3f}%  増 {100*c[f"{g}|増"]/max(dd,1):7.3f}%'
              + (' ★★★ **|V\'| < |Q| が 100%**'
                 if c[f'{g}|同'] == 0 and c[f'{g}|増'] == 0 and dd else ''))
    print(f'  ★★★ **L3 の主張の再現**: L3 の越境で `|V\'| < |Q|` が '
          f'{c["[L3b 越境] |V*| < |Q| ? True"]} 件、'
          f'⛔ **そうでない** {c["[L3b 越境] |V*| < |Q| ? False"]} 件')
    for x in ex:
        print(f'      ⛔ 私の越境で |V\'| >= |Q| の例: X={x[0]} n={x[1]} '
              f'r={x[2]} |Q|={x[3]} r2={x[4]} |V\'|={x[5]} bs={x[6]}')
    print()


if __name__ == '__main__':
    Ms = [list(m) for m in load()]
    print('## ⛔ L3 の箱に近い形（シート由来、|Q|<=5, n<=2）')
    run([M for M in Ms if len(M) <= 6], (1, 2), 4, 'シート |M|<=6, n<=2')
    print('## ★★ 大きい箱')
    SW = [list(x) for x in subwins(Ms, 8) if len(x) >= 3]
    S = SW if len(SW) <= 4000 else rng.sample(SW, 4000)
    run(S, (1, 2, 3), 4, f'★ シートの drop/take（標本 {len(S)}）, n<=3')
    run([list(m) for m in Ms], (1, 2, 3), 4, 'シート行列そのもの, n<=3')
