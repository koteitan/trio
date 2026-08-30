# -*- coding: utf-8 -*-
"""**課題 R92 —— 「等式が無条件」と「所属が閉じる」を分ける。**

§139 の残核: **`z = 1` かつ `c = 1` かつ `srow = 2` かつ「親が根でない」**。
team-lead の問い: 親が根でないなら `j0 >= 1` ⟹ **(P1) `oper_cons_nat` の枝**のはず。
だが `oper_cons_nat` が無条件なのは **等式** `S⟦n⟧ = (0,v,z) :: R⟦n⟧` であって、
**所属** `(0,v,z) :: R⟦n⟧ ∈ W a` ではない。そこを分けて測る。

測ること:

  (R92-a) 残核の形の入口はどの分岐に落ちるか（P1 / P3 / P2 のどれか）
  (R92-b) **所属**が閉じるか。健全な判定器 `inW`（`Wchar.lean` の厳密な特徴づけのみ）で
          ok / **VIOL（確定した非所属）** / unknown（予算切れ）の 3 分類
  (R92-c) **再帰が `CoreCap` の形に留まるか**。P1 の枝で
          `R⟦n⟧` が `argOK` か、かつ **`CtxOK (R⟦n⟧) (v+t) z`** が成り立つか
          （成り立てば帰納法の仮定がそのまま当たる。成り立たない場所が本当の残核）

⚠ 神託ゼロ。`inW` は展開して `lev > a` の単元に届いたときだけ False を返す（健全な反証）。
"""
import sys, itertools, time, argparse
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools')
import trio
from collections import Counter
from r89 import lift1, shape, cap, lev, inW

NS = (1, 2, 3)


def ctxOK(X, v, z, TS, depth, maxlen, memo):
    """`CtxOK X v z` を健全に判定。'eq' / 'NOT-eq' / 'unk'。"""
    st = 'eq'
    for k in range(len(X)):
        for t in TS:
            r = inW(lift1([(0, v, z)] + list(X[:k]), t), 2 * (v + t) + z,
                    depth, memo, maxlen)
            if r is False:
                return 'NOT-eq'
            if r is None and st == 'eq':
                st = 'unk'
    return st


def run(DS, BS, CS, VS, TS, CAPB, LS, depth, maxlen, label):
    """残核の形だけを走らせる: z = 1, c = 1。"""
    COL = [(d, b, c) for d in DS for b in BS for c in CS]
    memo = {}
    br_cnt = Counter(); mem = Counter(); prop = Counter(); ex = {}
    z, c = 1, 1
    t0 = time.time()
    for L in LS:
        for Mt in itertools.product(COL, repeat=L):
            M = list(Mt)
            for v in VS:
                for t in TS:
                    S = lift1([(0, v, z)] + cap(M, 0, c), t)   # b は下で振る
                    for b in CAPB:
                        S = lift1([(0, v, z)] + cap(M, b, c), t)
                        j1 = len(S) - 1
                        if S[j1][2] == 0:
                            continue
                        brn, j0, i1, d0, d1 = shape(S)
                        if i1 != 2:
                            continue
                        # 「親が根でない」= j0 != 0（noparent も含めて記録）
                        tag = brn if brn != 'copy' else ('tower(j0=0)' if j0 == 0
                                                         else 'cons(j0>=1)')
                        br_cnt[tag] += 1
                        if brn == 'copy' and j0 == 0:
                            continue          # 残核ではない（親が根）
                        # ---- (R92-b) 所属 ----
                        a = 2 * (v + t) + z
                        r = inW(S, a, depth, memo, maxlen)
                        key = 'VIOL' if r is False else 'ok' if r is True else 'unknown'
                        mem[tag + '/' + key] += 1
                        if r is False:
                            ex.setdefault('VIOL', (M, v, z, b, c, t, S))
                        # ---- (R92-c) 再帰が CoreCap の形に留まるか ----
                        if brn == 'copy':
                            for n in NS:
                                R2 = trio.expand(list(S[1:]), n)
                                if not R2:
                                    prop['R[n] 空'] += 1; continue
                                ag = all(q[0] >= 1 for q in R2)
                                prop['argOK/' + ('ok' if ag else 'VIOL')] += 1
                                st = ctxOK(R2, S[0][1], z, TS, depth, maxlen, memo)
                                prop['CtxOK/' + st] += 1
                                if st == 'NOT-eq':
                                    ex.setdefault('CtxOK-NOT', (M, v, z, b, c, t, n, R2))
                                if not ag:
                                    ex.setdefault('argOK-NOT', (M, v, z, b, c, t, n, R2))
    dt = time.time() - t0
    print(f'### {label}  ({dt:.1f}s, memo={len(memo)})')
    print('  -- (R92-a) 残核の形 (z=1, c=1, srow=2) の分岐 --')
    for k in sorted(br_cnt):
        print(f'     {k:16s} {br_cnt[k]:10d}')
    print('  -- (R92-b) **所属**（健全な判定器） --')
    for k in sorted(mem):
        print(f'     {k:24s} {mem[k]:10d}')
    print('  -- (R92-c) 再帰は CoreCap の形に留まるか --')
    for k in sorted(prop):
        print(f'     {k:20s} {prop[k]:10d}')
    for k in sorted(ex):
        print(f'  ex {k}: {ex[k]}')
    print()


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=3)
    ap.add_argument('--depth', type=int, default=9)
    a = ap.parse_args()
    run((1, 2, 3), (0, 1, 2), (0, 1), (0, 1, 2), (0, 1, 2), (0, 1, 2, 3),
        tuple(range(1, a.L + 1)), a.depth, 26,
        f'R92 残核 z=1,c=1,srow=2 |M|<={a.L} depth={a.depth}')


def control(depth=9, maxlen=26):
    """**陽性対照**: 健全な判定器 `inW` が確定 False を返すことを見せる。
    かつ `ctxOK` が `NOT-eq` を返す例を作る（教訓 12: 鳴らない計器は無価値）。"""
    memo = {}
    print('### R92 陽性対照')
    cases = [
        ([(0, 1, 0)], 0, '単元 lev 2 > a=0'),
        ([(0, 0, 1)], 0, '単元 lev 1 > a=0'),
        ([(0, 0, 0), (1, 1, 1)], 0, '塔が lev 2 の単元に届く?'),
        ([(0, 0, 0), (1, 2, 1)], 1, '同上 a=1'),
    ]
    for S, a, note in cases:
        print(f'  inW({S}, a={a}) = {inW(S, a, depth, memo, maxlen)}   {note}')
    # ctxOK の陽性対照: **段を 1 だけ小さく**すると k=0 の接頭辞
    # `[(0,v+t,z)]`（lev = 2(v+t)+z）が入らなくなるので NOT-eq が鳴るはず
    def ctxOK_off(X, v, z, TS, off):
        st = 'eq'
        for k in range(len(X)):
            for t in TS:
                r = inW(lift1([(0, v, z)] + list(X[:k]), t),
                        2 * (v + t) + z - off, depth, memo, maxlen)
                if r is False:
                    return 'NOT-eq'
                if r is None and st == 'eq':
                    st = 'unk'
        return st
    for X, v, z in ([[(1, 3, 1), (1, 0, 0)], 1, 1], [[(1, 0, 0)], 1, 1]):
        print(f'  ctxOK({X}, v={v}, z={z})            = '
              f'{ctxOK_off(X, v, z, (0, 1, 2), 0)}')
        print(f'  ctxOK({X}, v={v}, z={z})  段 -1     = '
              f'{ctxOK_off(X, v, z, (0, 1, 2), 1)}   ← 対照。鳴るはず')
