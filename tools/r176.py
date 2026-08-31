# -*- coding: utf-8 -*-
"""**課題 (w2) —— 「復活の回数」は測度の材料になるか。**

**「復活」の定義（この測定での操作的定義。明記する）**:

    段の合成列 `S = mTower Q d e n ++ B.take (j+1)`、`last = n*|Q| + j`、`par = 親`。
    **復活 = `par < n*|Q|`**（親が**塔の中**＝**前のブロック**にある）
    非復活 = `par >= n*|Q|`（親が**いま足しているブロックの中**）

`|V| = last - par` なので、**復活 ⟺ `|V| > j`**。

## ★ 予想（教訓 45）＋ 見積もり
> (w1) で「決め打ちの鎖は最大 2 段」が出たので、(w2) の主戦場は**自由な鎖**。
> **⚠ 見積もり: 自由な鎖の 30 段のうち復活が起きるのは 40〜70%。**
> **⚠ (w2c) 非復活だけの鎖は 5 段以内で止まると予想（`|V| <= j < |Q|` で頭打ちのため）。**
> **⚠ 反例の形: 非復活だけで `|V|` が非減少のまま 30 段続く鎖。**

**`W` 所属は判定しない。**
"""
import sys, time, random, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block

COL4 = [(a, b, c) for a in range(4) for b in range(4) for c in (0, 1)]


def step_full(Q, d, e, n, j):
    """`(V, d', e', 復活か)` を返す。"""
    T = [tuple(x) for x in mTower(Q, d, e, n)]
    S = T + block(Q, d, e, n)[:j + 1]
    last = len(S) - 1
    i1 = srow(S, last)
    par = trio.parent(S, i1, last)
    if par is None: return None
    d2 = (S[last][0] - S[par][0]) if i1 > 0 else 0
    e2 = (S[last][1] - S[par][1]) if i1 > 1 else 0
    return S[par:last], d2, e2, (par < len(T))


def chain(Q0, cap, NS, DE, free, revival_ok, rnd):
    """非減少 (`|V'| >= |V|`) の鎖を貪欲＋ランダム順で伸ばす。
    `revival_ok=False` なら**復活する段を使わない**（(w2c)）。"""
    cur, d, e = list(Q0), rnd.choice(DE), rnd.choice(DE)
    nrev = 0; s = 0; seq = [len(cur)]; revs = []
    while s < cap:
        cands = []
        DD = [(dd, ee) for dd in DE for ee in DE] if free else [(d, e)]
        for (dd, ee) in DD:
            for n in NS:
                for j in range(len(cur)):
                    r = step_full(cur, dd, ee, n, j)
                    if r is None or len(r[0]) < len(cur) or len(r[0]) < 2: continue
                    if (not revival_ok) and r[3]: continue
                    cands.append(r)
        if not cands: break
        rnd.shuffle(cands)
        V, d, e, rev = cands[0]
        cur = list(V); nrev += 1 if rev else 0; revs.append(rev)
        seq.append(len(cur)); s += 1
    return s, nrev, seq, revs


def run(tag, free, revival_ok, nsamp, cap, seed):
    rnd = random.Random(seed); c = Counter(); allrev = []
    t0 = time.time()
    for _ in range(nsamp):
        L = rnd.randrange(3, 7)
        root = rnd.choice(COL4); hi = [x for x in COL4 if x[0] > root[0]]
        if not hi: continue
        Q0 = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        s, nrev, seq, revs = chain(Q0, cap, (2, 3), range(4), free, revival_ok, rnd)
        c['本数'] += 1; c[('段', min(s, 10))] += 1
        c['段の総和'] += s; c['復活の総和'] += nrev
        if s >= cap: c['★ cap まで続いた'] += 1
        allrev += revs
    t = c['本数']
    print(f'### {tag}  本数 {t}  cap={cap}  [{time.time()-t0:.1f}s]')
    print('    段数分布: ', dict(sorted((k[1], c[k]) for k in c if isinstance(k, tuple))))
    print(f'    **★ cap まで続いた … {c["★ cap まで続いた"]} / {t} '
          f'({100*c["★ cap まで続いた"]/max(t,1):6.2f}%)**')
    if c['段の総和']:
        print(f'    (w2a) 復活が起きた段 … {c["復活の総和"]} / {c["段の総和"]} '
              f'({100*c["復活の総和"]/c["段の総和"]:6.2f}%)')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--n', type=int, default=200)
    ap.add_argument('--cap', type=int, default=30); a = ap.parse_args()
    run('(w2a) 自由な鎖（(n2) の鎖）で復活はどれくらい起きるか', True,  True,  a.n, a.cap, 31)
    run('(w2c) ★ 復活する段を禁止した鎖（自由）',                  True,  False, a.n, a.cap, 31)
    run('(w2c) 復活する段を禁止した鎖（`(d,e)` 決め打ち）',        False, False, a.n, a.cap, 31)
    run('   参考: `(d,e)` 決め打ち・復活を許す',                    False, True,  a.n, a.cap, 31)
