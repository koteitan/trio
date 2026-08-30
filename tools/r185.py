# -*- coding: utf-8 -*-
"""(u1d) の訂正: r184 の母集団は **`hr0` を自動で満たしていた**（生成器が
`Q[l][0] > Q[0][0]` を課していた）⟹ `hr0` を落とせるかは測れていなかった。

**根の行 0 が最小とは限らない `Q`** も入れて測り直す。
"""
import sys, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from collections import Counter
from r183 import hr0, hnb, hz0, probe


def run(E, LS, NS, DE, nsamp, seed):
    COL = [(x, y, z) for x in range(E) for y in range(E) for z in (0, 1)]
    rnd = random.Random(seed); c = Counter(); ex = []
    for _ in range(nsamp):
        L = rnd.choice(LS)
        Q = [rnd.choice(COL) for _ in range(L)]      # ← 制約なしで生成
        d, e, n = rnd.choice(DE), rnd.choice(DE), rnd.choice(NS)
        conds = {'前提なし': True, 'hr0': hr0(Q), 'hnb': hnb(Q), 'hz0': hz0(Q),
                 'hr0∧hz0': hr0(Q) and hz0(Q), 'hnb∧hz0': hnb(Q) and hz0(Q),
                 '⚠ hz0 のみ(hr0 なし)': hz0(Q) and not hr0(Q),
                 '3 つ全部': hr0(Q) and hnb(Q) and hz0(Q)}
        for j in range(1, L):
            r = probe(Q, d, e, n, j)
            if r is None: continue
            lv, par, inblk = r
            for k, ok in conds.items():
                if not ok: continue
                c[(k, '段')] += 1
                if lv >= L:
                    c[(k, '非減少')] += 1
                    if k == '⚠ hz0 のみ(hr0 なし)' and len(ex) < 4:
                        ex.append((Q, d, e, n, j, lv))
                if not inblk: c[(k, '外')] += 1
    print(f'### (u1d 訂正) 制約なしの `Q`  値域<{E} |Q|∈{LS}  （`j>=1` の段だけ）')
    print(f'    {"前提":22s} {"段":>9s} {"⚠ 非減少":>16s} {"⚠ 親がブロックの外":>18s}')
    for k in ['前提なし', 'hr0', 'hnb', 'hz0', 'hr0∧hz0', 'hnb∧hz0',
              '⚠ hz0 のみ(hr0 なし)', '3 つ全部']:
        t = c[(k, '段')]
        if not t: continue
        print(f'    {k:22s} {t:9d} {c[(k,"非減少")]:7d} ({100*c[(k,"非減少")]/t:7.4f}%) '
              f'{c[(k,"外")]:9d} ({100*c[(k,"外")]/t:7.4f}%)')
    for x in ex: print(f'      ⚠ 例 Q={x[0]} d={x[1]} e={x[2]} n={x[3]} j={x[4]} |V|={x[5]}')
    print()


if __name__ == '__main__':
    run(4, (3,4,5,6),   (2,3,4),   range(4), 60000, 141)
    run(6, (3,4,5,6,8), (2,3,4,5), range(6), 60000, 143)
    run(9, (4,6,8,10),  (2,3,4,5), range(9), 40000, 145)
