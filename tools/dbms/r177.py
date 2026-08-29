# -*- coding: utf-8 -*-
"""(w1) の**山**を壊しにいく（教訓 21）。

r175 の結果:
    直前が**減少**   ⟹ 次も非減少 **28.74%**
    直前が**非減少** ⟹ 次も非減少 **0.00%（0 / 527）**  ← ⚠ 分母が小さい。壊しにいく。

r174 の広い箱では**段 2 が 2 本／5 本**出ていた。**つまり 0% は破れる。**
ここで分母を 10^5 級にし、箱を広げ、**非減少の連（run）の最大長**を出す。

**測る量**: `(d,e)` 決め打ちで **`|V'| >= |V|` の段を連続して何段つなげるか**の最大。
（BFS 全探索。状態 `(V, d, e)` で重複除去。）

## ★ 予想（教訓 45）
> **⚠ 見積もり: 連の最大長は 2〜3。長さ 2 以上になる割合は 1% 未満。**
> **⚠ 反例の形: 30 段の連。出たら (n2) は決め打ちでも堅牢。**
"""
import sys, time, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from collections import Counter
from r171 import step_det


def runlen(Q, d, e, cap, NS, beam):
    """`(Q,d,e)` から**非減少の段だけ**で何段つなげるか（BFS 全探索、上限 cap）。"""
    front = [(tuple(map(tuple, Q)), d, e)]
    best = 0
    for s in range(cap):
        nxt = set()
        for (V, dd, ee) in front:
            for n in NS:
                for j in range(len(V)):
                    r = step_det(list(V), dd, ee, n, j)
                    if r is None or len(r[0]) < len(V) or len(r[0]) < 2: continue
                    nxt.add((tuple(r[0]), r[1], r[2]))
        if not nxt: return best
        best = s + 1
        front = list(nxt)
        if len(front) > beam:
            random.shuffle(front); front = front[:beam]
    return best


def run(E, LS, NS, DE, nsamp, cap, seed, beam=3000):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); random.seed(seed)
    c = Counter(); ex = []; t0 = time.time()
    tries = 0
    while c['母集団(非減少の段の出力)'] < nsamp and tries < nsamp * 200:
        tries += 1
        L = rnd.choice(LS)
        root = rnd.choice(COL); hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q0 = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d0, e0 = rnd.choice(DE), rnd.choice(DE)
        n0, j0 = rnd.choice(NS), rnd.randrange(L)
        r = step_det(Q0, d0, e0, n0, j0)
        if r is None or len(r[0]) < len(Q0) or len(r[0]) < 2:
            continue                      # ← 直前の段が非減少だったものだけを母集団に
        V, d, e = r
        c['母集団(非減少の段の出力)'] += 1
        rl = runlen(V, d, e, cap, NS, beam)
        c[('連の追加長', min(rl, 8))] += 1
        if rl >= 1:
            c['⚠ もう 1 段つながる'] += 1
            if len(ex) < 5: ex.append((Q0, d0, e0, n0, j0, V, d, e, rl))
        if rl >= cap: c['★ cap まで'] += 1
    t = c['母集団(非減少の段の出力)']
    print(f'### 値域<{E} |Q0|∈{LS} n∈{tuple(NS)} (d,e)∈{tuple(DE)} cap={cap}  '
          f'母集団 {t}  [{time.time()-t0:.1f}s]')
    print('    追加でつながった段数の分布: ',
          dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    print(f'    **⚠ 非減少がもう 1 段つながる … {c["⚠ もう 1 段つながる"]} / {t} '
          f'({100*c["⚠ もう 1 段つながる"]/max(t,1):7.4f}%)**')
    print(f'    ★ {cap} 段つながった … {c["★ cap まで"]} / {t}')
    for x in ex[:3]:
        print(f'      ⚠ 例 Q0={x[0]} (d,e)=({x[1]},{x[2]}) n={x[3]} j={x[4]} '
              f'⟹ V={x[5]} (d\',e\')=({x[6]},{x[7]}) さらに {x[8]} 段')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--n', type=int, default=20000)
    ap.add_argument('--cap', type=int, default=20); a = ap.parse_args()
    run(4, (3, 4, 5, 6),    (2, 3),          range(4), a.n, a.cap, 41)
    print('#### 教訓 21: 箱を広げる')
    run(6, (4, 6, 8),       (1, 2, 3, 4, 5), range(6), a.n, a.cap, 43)
    run(9, (6, 8, 10, 12),  (1, 2, 3, 4, 6), range(9), a.n // 2, a.cap, 47)
