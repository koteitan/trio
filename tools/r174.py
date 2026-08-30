# -*- coding: utf-8 -*-
"""(w1b) 決着。r172（鎖 0/600）と r173（25% は減らない）の食い違いを潰す。

**仮説**: r172 は**貪欲**（最初に見つかった `(n,j)` を採る）だった。
2 段目まで**全探索**すれば残るかもしれない。

**測る量**: `(d,e)` を `oper` 決め打ちにしたとき、`|V|` が減らない鎖の**最大段数**を
**全探索（幅優先、状態を正規化して重複除去）**で求める。

## ★ 予想（教訓 45）
> r173 が 25% と言っているので、**2 段以上続く鎖は存在する**と予想。
> **⚠ 見積もり: 最大段数の中央値 2〜4、最大 10 以上が数 % 出る。**
> **⚠ (n2) が本当に堅牢かは「30 段以上」が出るかどうかで決まる。**
"""
import sys, time, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from collections import Counter
from r171 import step_det

BEAM = 400


def deepest(Q0, d0, e0, cap, NS, beam=BEAM):
    """`|V|` が減らない鎖の最大段数（ビーム幅 `beam` の全探索）。到達した段と例を返す。"""
    front = [(tuple(map(tuple, Q0)), d0, e0, [len(Q0)])]
    best = 0; bex = None
    for s in range(cap):
        nxt = []; seen = set()
        for (Q, d, e, seq) in front:
            for n in NS:
                for j in range(len(Q)):
                    r = step_det(list(Q), d, e, n, j)
                    if r is None: continue
                    V, d2, e2 = r
                    if len(V) < len(Q) or len(V) < 2: continue
                    key = (tuple(V), d2, e2)
                    if key in seen: continue
                    seen.add(key)
                    nxt.append((tuple(V), d2, e2, seq + [len(V)]))
        if not nxt:
            return best, bex
        best = s + 1; bex = nxt[0][3]
        random.shuffle(nxt)
        front = nxt[:beam]
    return best, bex


def run(L, E, NS, DE, nsamp, cap, seed):
    COL = [(a, b, c) for a in range(E) for b in range(E) for c in (0, 1)]
    rnd = random.Random(seed); random.seed(seed)
    c = Counter(); t0 = time.time(); mxs = []
    ex = None
    for _ in range(nsamp):
        root = rnd.choice(COL)
        hi = [x for x in COL if x[0] > root[0]]
        if not hi: continue
        Q0 = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d0, e0 = rnd.choice(DE), rnd.choice(DE)
        s, seq = deepest(Q0, d0, e0, cap, NS)
        c['母集団'] += 1; mxs.append(s)
        c[('段', min(s, 10))] += 1
        if s >= cap:
            c['★ cap まで続いた'] += 1
            if ex is None: ex = (Q0, d0, e0, seq)
    tot = c['母集団']
    mxs.sort()
    print(f'### |Q0|={L} 値域<{E} n∈{tuple(NS)} 初期(d,e)∈{tuple(DE)} cap={cap} '
          f'母集団 {tot}  [{time.time()-t0:.1f}s]')
    print('  最大段数の分布: ', dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    print(f'  中央値 {mxs[len(mxs)//2]}   最大 {mxs[-1]}   '
          f'**★ cap({cap}) まで … {c["★ cap まで続いた"]} / {tot} '
          f'({100*c["★ cap まで続いた"]/max(tot,1):6.2f}%)**')
    if ex: print(f'      続いた例 Q0={ex[0]} (d,e)=({ex[1]},{ex[2]}) `|V|`の列={ex[3][:16]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=300); ap.add_argument('--cap', type=int, default=30)
    a = ap.parse_args()
    for L in (3, 4, 5):
        run(L, 4, (2, 3), range(4), a.n, a.cap, 5)
    print('#### 教訓 21: 箱を広げる')
    for L in (4, 6):
        run(L, 6, (1, 2, 3, 4, 5), range(6), a.n, a.cap, 9)
