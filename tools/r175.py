# -*- coding: utf-8 -*-
"""(w1) の**検算と対照**。3 つやる。

1. **検算(fidelity)**: `step_det` が返す `(V, d', e')` が**本物の `oper`** と一致するか。
   `Trio.lean:109-114` を逐語で組み立てて `trio.expand` と突き合わせる。
   ここがずれていたら (w1) の結論は全部無効。
2. **陽性対照**: 同じ全探索で `(d,e)` を**毎段自由**にすると 30 段届くか（届くべき）。
3. **食い違いの説明**: r173(25% は減らない) と r174(最大 2 段) の差は
   「**直前の段が非減少だったか**」で説明できるか。
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow
from r113 import mTower
from r141 import block
from r171 import step_det
from r98 import oper_lean
from r174 import deepest

COL4 = [(a, b, c) for a in range(4) for b in range(4) for c in (0, 1)]


def le0(S, a, b):
    return trio.le0(S, a, b) if hasattr(trio, 'le0') else None


# ---------- 1. 検算 ----------
def fidelity(nsamp, seed):
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.randrange(2, 6)
        root = rnd.choice(COL4); hi = [x for x in COL4 if x[0] > root[0]]
        if not hi: continue
        Q = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e, n, j = rnd.randrange(4), rnd.randrange(4), rnd.choice((2, 3)), rnd.randrange(L)
        T = [tuple(x) for x in mTower(Q, d, e, n)]
        S = T + block(Q, d, e, n)[:j + 1]
        last = len(S) - 1
        i1 = srow(S, last)
        par = trio.parent(S, i1, last)
        if par is None: continue
        c['母集団'] += 1
        # 切り捨て引き算が起きていないか（教訓: 前に踏んだ罠）
        if i1 > 0 and S[last][0] < S[par][0]: c['⚠ 行0 で切り捨て'] += 1
        if i1 > 1 and S[last][1] < S[par][1]: c['⚠ 行1 で切り捨て'] += 1
        d2 = (S[last][0] - S[par][0]) if i1 > 0 else 0
        e2 = (S[last][1] - S[par][1]) if i1 > 1 else 0
        for m in (1, 2, 3):
            # Trio.lean:109-114 の逐語
            want = list(S[:par])
            for k in range(m):
                for jj in range(par, last):
                    a0 = S[jj][0] + (k * d2 if trio.is_ancestor(S, 0, par, jj) else 0)
                    a1 = S[jj][1] + (k * e2 if trio.is_ancestor(S, 1, par, jj) else 0)
                    want.append((a0, a1, S[jj][2]))
            got = oper_lean([list(x) for x in S], m)
            if [tuple(x) for x in got] == want: c[f'一致 m={m}'] += 1
            else:
                c[f'⚠ 不一致 m={m}'] += 1
                if c[f'⚠ 不一致 m={m}'] <= 2:
                    print('   ⚠ 不一致例 S=', S, 'par=', par, 'd2,e2=', d2, e2)
                    print('      want=', want[:8]); print('      got =', got[:8])
    print('### 1. 検算: `step_det` の `(V,d\',e\')` は本物の `oper` と一致するか')
    for k in sorted(c): print(f'    {k:22s} {c[k]}')
    ok = all(c[f'⚠ 不一致 m={m}'] == 0 for m in (1, 2, 3)) and c['⚠ 行0 で切り捨て'] == 0
    print(f'  **⟹ {"★ 一致（(w1) の結論は有効）" if ok else "⚠ ずれあり — 結論は無効"}**\n')


# ---------- 2. 陽性対照 ----------
def deepest_free(Q0, cap, NS, DE, beam=200):
    front = [(tuple(map(tuple, Q0)), [len(Q0)])]
    best = 0
    for s in range(cap):
        nxt = []; seen = set()
        for (Q, seq) in front:
            for d in DE:
                for e in DE:
                    for n in NS:
                        for j in range(len(Q)):
                            r = step_det(list(Q), d, e, n, j)
                            if r is None or len(r[0]) < len(Q) or len(r[0]) < 2: continue
                            k = tuple(r[0])
                            if k in seen: continue
                            seen.add(k); nxt.append((k, seq + [len(r[0])]))
        if not nxt: return best
        best = s + 1; random.shuffle(nxt); front = nxt[:beam]
    return best


def control(nsamp, cap, seed):
    rnd = random.Random(seed); random.seed(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.randrange(3, 6)
        root = rnd.choice(COL4); hi = [x for x in COL4 if x[0] > root[0]]
        if not hi: continue
        Q0 = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        c['母集団'] += 1
        if deepest_free(Q0, cap, (2, 3), range(4)) >= cap: c['★ 30段届いた(自由)'] += 1
        if deepest(Q0, rnd.randrange(4), rnd.randrange(4), cap, (2, 3))[0] >= cap:
            c['⚠ 30段届いた(決め打ち)'] += 1
    t = c['母集団']
    print('### 2. 陽性対照（同じ全探索、`(d,e)` 自由 vs 決め打ち）')
    print(f'    自由     … {c["★ 30段届いた(自由)"]:4d} / {t} ({100*c["★ 30段届いた(自由)"]/max(t,1):6.2f}%)  ← 鳴るべき')
    print(f'    決め打ち … {c["⚠ 30段届いた(決め打ち)"]:4d} / {t} ({100*c["⚠ 30段届いた(決め打ち)"]/max(t,1):6.2f}%)\n')


# ---------- 3. 食い違いの説明 ----------
def reconcile(nsamp, seed):
    rnd = random.Random(seed); c = Counter()
    for _ in range(nsamp):
        L = rnd.randrange(3, 7)
        root = rnd.choice(COL4); hi = [x for x in COL4 if x[0] > root[0]]
        if not hi: continue
        Q0 = [root] + [rnd.choice(hi) for _ in range(L - 1)]
        d, e = rnd.randrange(4), rnd.randrange(4)
        r = step_det(Q0, d, e, rnd.choice((2, 3)), rnd.randrange(L))
        if r is None or len(r[0]) < 2: continue
        V, d2, e2 = r
        grew = len(V) >= len(Q0)           # ← 直前の段が非減少だったか
        tag = '直前が非減少' if grew else '直前が減少'
        c[tag] += 1
        nxt = max((len(step_det(V, d2, e2, n, j)[0])
                   for n in (2, 3) for j in range(len(V))
                   if step_det(V, d2, e2, n, j)), default=-1)
        if nxt >= len(V): c[tag + ' ⟹ 次も非減少'] += 1
    print('### 3. r173(25%) と r174(最大2段) の食い違いの説明')
    for t in ('直前が減少', '直前が非減少'):
        print(f'    {t:12s} {c[t]:6d} 本 ⟹ 次も非減少 {c[t+" ⟹ 次も非減少"]:6d} '
              f'({100*c[t+" ⟹ 次も非減少"]/max(c[t],1):6.2f}%)')
    print()


if __name__ == '__main__':
    fidelity(400, 3)
    control(200, 30, 4)
    reconcile(20000, 5)
