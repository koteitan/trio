# -*- coding: utf-8 -*-
"""**課題 (p1)（team-lead の依頼）—— 「減らない鎖」の上で何が変化するかを総当たり。**

**鎖**: `M = mTower Q d e n ++ Bn.take (j+1)`、`par` を悪根、`V = M[par:last]`、`Q := V`。
各段で `(d,e,n,j)` を「`|V| >= |Q|` になるように」貪欲に選ぶ（§R164-4 の鎖）。

## ★ 予想を先に書く（教訓 45）＋ 見積もり

> **(p1d) 鎖は**無限に続く**はず。理由: `V` の成分は `oper` のずらしで**増える**ので、
> 各段の `Q` は毎回新しく、有限集合に閉じ込められない ⟹ 鳩の巣が効かない。**
> **⚠ 見積もり: 100 段でも止まらない。**
>
> **(p1b) 単調に減る量は**無い**はず。⚠ 見積もり: 0 個。**
> **(p1c) 単調に増える量は**ある**はず（根の行 0、成分の和、最大値）。**
> **⟹ ただし上界が無いので停止性は出ない。**

**箱と単位**: 鎖 1 本 ＝ `(Q0, 各段の選択)`。`|Q0| = 3..4`、`d,e ∈ 0..3`、`n ∈ 2..3`。
**`W` 所属は判定しない（明記）。**
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import trio
from collections import Counter
from r126 import srow, le1_root
from r113 import mTower
from r141 import block


def step(Q, d, e, n, j):
    L = len(Q)
    T = [tuple(x) for x in mTower(Q, d, e, n)]
    Bn = block(Q, d, e, n)
    S = T + Bn[:j + 1]
    last = len(S) - 1
    par = trio.parent(S, srow(S, last), last)
    if par is None:
        return None
    return S[par:last]


def stats(Q):
    """記録する量。"""
    L = len(Q)
    return {
        '|V|': L,
        '錐の外の本数': sum(1 for i in range(1, L) if not le1_root(Q, i)),
        '行2が正の本数': sum(1 for i in range(L) if Q[i][2] > 0),
        '孤児の本数': sum(1 for i in range(L)
                       if trio.parent(Q[:i + 1], srow(Q, i), i) is None),
        'maxlev': max(2 * p[1] + p[2] for p in Q),
        '根のlev': 2 * Q[0][1] + Q[0][2],
        '根の行0': Q[0][0],
        '成分の和': sum(p[0] + p[1] + p[2] for p in Q),
        '行1の最大': max(p[1] for p in Q),
        '行0の最大': max(p[0] for p in Q),
    }


def chain(Q0, cap, DE, NS):
    """`|V| >= |Q|` を貪欲に選ぶ鎖。各段の stats を返す。"""
    cur = list(Q0); rec = [stats(cur)]; picks = []
    for _ in range(cap):
        nxt = None
        for d in DE:
            for e in DE:
                for n in NS:
                    for j in range(len(cur)):
                        V = step(cur, d, e, n, j)
                        if V and len(V) >= len(cur):
                            nxt = list(V); picks.append((d, e, n, j)); break
                    if nxt: break
                if nxt: break
            if nxt: break
        if nxt is None:
            return rec, picks, '止まった'
        cur = nxt; rec.append(stats(cur))
    return rec, picks, '打ち切り'


def run(L, cap, DE, NS, nsample):
    COL = [(a, b, c) for a in range(4) for b in range(3) for c in (0, 1)]
    t0 = time.time(); done = 0
    keys = list(stats([(0, 0, 0), (1, 0, 0)]).keys())
    agg = Counter()
    print(f'### |Q0|={L}  鎖を {cap} 段まで  [開始]')
    for root in COL:
        for t in itertools.product([x for x in COL if x[0] > root[0]], repeat=L - 1):
            Q0 = [root] + list(t)
            if step(Q0, 2, 2, 2, 0) is None:
                continue
            rec, picks, how = chain(Q0, cap, DE, NS)
            if len(rec) < cap + 1 and how == '止まった':
                agg[('止まった段数', len(rec) - 1)] += 1
                continue
            agg['最後まで続いた'] += 1
            for k in keys:
                seq = [r[k] for r in rec]
                if all(seq[i] > seq[i + 1] for i in range(len(seq) - 1)):
                    agg[('★ 単調減少', k)] += 1
                if all(seq[i] < seq[i + 1] for i in range(len(seq) - 1)):
                    agg[('★ 単調増加', k)] += 1
                if all(seq[i] >= seq[i + 1] for i in range(len(seq) - 1)):
                    agg[('非増加', k)] += 1
            if done < 2:
                print(f'  例 Q0={Q0}')
                for k in keys:
                    print(f'      {k:14s}: {[r[k] for r in rec][:13]}')
                print(f'      選んだ (d,e,n,j): {picks[:6]}…')
            done += 1
            if done >= nsample:
                break
        if done >= nsample:
            break
    print(f'  **最後まで（{cap} 段）続いた鎖: {agg["最後まで続いた"]}**   '
          f'止まった段数: ' + str(dict(sorted((k[1], agg[k]) for k in agg
                                       if isinstance(k, tuple) and k[0] == '止まった段数'))))
    tot = agg['最後まで続いた']
    if tot:
        print('  **★ (p1b) 単調減少した量**: ', {k[1]: agg[k] for k in agg
                                        if isinstance(k, tuple) and k[0] == '★ 単調減少'} or '**無し**')
        print('  **★ (p1c) 単調増加した量**: ', {k[1]: agg[k] for k in agg
                                        if isinstance(k, tuple) and k[0] == '★ 単調増加'} or '無し')
        print('  非増加（減るか同じ）の量: ', {k[1]: agg[k] for k in agg
                                     if isinstance(k, tuple) and k[0] == '非増加'})
    print(f'  [{time.time()-t0:.1f}s]\n')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--cap', type=int, default=30)
    ap.add_argument('--L', type=int, default=3)
    a = ap.parse_args()
    run(a.L, a.cap, range(4), (2, 3), 40)
