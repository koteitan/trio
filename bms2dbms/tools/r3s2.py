# -*- coding: utf-8 -*-
"""課題 R3: 像のバッドルート `r'` を `A` と `conv3` の構造から書く。

仮説（`t` で場合分け）:

    j0 = pim(A)[last][t-1]        末尾列の**行 t-1 の親**
    cand_sh = 「列 j0 が出した `sh(t-1)` の柱」の像での添字
    cand_bd = img r（列 r の本体柱）
    r' = max(有効な候補)          （バッドルートは「直前でいちばん近い」ので）
"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, provc, core
from rows3 import gen3, key
from core import pim, show


def badroot(S):
    X = len(S)
    if X < 2:
        return None
    x = X - 1
    Y = len(S[0])
    if all(v == 0 for v in S[x]):
        return None
    t = max(y for y in range(Y) if S[x][y] > 0)
    r = pim(S)[x][t]
    if r == -1:
        return None
    return t, r


def prov(M):
    C, PR = provc.b2d3p(list(M))
    return C, PR


def pillars(PR, j):
    return [(i, e[0]) for i, e in enumerate(PR) if e[1] == j]


def relpos(off, r, last):
    if off == last:
        return '=last'
    if off == r:
        return '=r'
    if r < off < last:
        return 'between'
    if off < r:
        return '<r'
    return '?'


def explore(pop, name, verbose=4):
    """`r'` が何者かを分布で見る。"""
    c = Counter(); ex = {}
    t0 = time.time()
    for n_, M in enumerate(pop):
        if n_ % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear()
            core._flat_memo.clear()
        S = tuple(map(tuple, M))
        br = badroot(S)
        if br is None:
            continue
        t, r = br
        B, PR = prov(S)
        B = tuple(map(tuple, B))
        br2 = badroot(B)
        if br2 is None:
            c['像の末尾が孤児'] += 1
            continue
        t2, r2 = br2
        c['_母数'] += 1; c['_t=%d' % t] += 1
        last = len(S) - 1
        kind, off = PR[r2][0], PR[r2][1]
        c['t=%d  %s @ %s' % (t, kind, relpos(off, r, last))] += 1
        k = (t, kind, relpos(off, r, last))
        if k not in ex:
            ex[k] = (S, B, t, r, r2, PR[r2], last,
                     [(i, e[0], e[1]) for i, e in enumerate(PR)])
    print('== %s  母数 %d（t=1 %d / t=2 %d）  (%.0fs)'
          % (name, c['_母数'], c['_t=1'], c['_t=2'], time.time() - t0))
    for k in sorted(c, key=str):
        if not k.startswith('_'):
            print('   %-34s %d' % (k, c[k]))
    for k, e in list(ex.items())[:verbose]:
        S, B, t, r, r2, pe, last, pl = e
        print('   例 %s' % str(k))
        print('      A = %s' % show([list(x) for x in S]))
        print('      B = %s' % show([list(x) for x in B]))
        print("      t=%d r=%d last=%d  r'=%d PROV=%s" % (t, r, last, r2, pe))
        print('      PROV = %s' % pl)
    return c


def run(pop, name, hyp, mode='real', verbose=3):
    """`hyp(S, PR, t, r, last)` が返す添字が `r'` と一致するか。"""
    c = Counter(); ex = {}
    t0 = time.time()
    for n_, M in enumerate(pop):
        if n_ % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear()
            core._flat_memo.clear()
        S = tuple(map(tuple, M))
        br = badroot(S)
        if br is None:
            continue
        t, r = br
        B, PR = prov(S)
        B = tuple(map(tuple, B))
        br2 = badroot(B)
        if br2 is None:
            continue
        t2, r2 = br2
        c['_母数'] += 1; c['_t=%d' % t] += 1
        last = len(S) - 1
        hyp.B = B
        pred = hyp(S, PR, t, r, last)
        if mode == 'P_plus1':
            pred = None if pred is None else pred + 1
        elif mode == 'P_img':
            bd = [i for i, e in enumerate(PR) if e[1] == r and e[0] == 'body']
            pred = bd[-1] if bd else None
        ok = (pred == r2)
        c['t=%d %s' % (t, 'OK' if ok else 'NG')] += 1
        if not ok:
            kk = (t, PR[r2][0] if r2 < len(PR) else '?',
                  relpos(PR[r2][1], r, last) if r2 < len(PR) else '?')
            c['NG %s' % str(kk)] += 1
            if kk not in ex:
                ex[kk] = (S, B, t, r, r2, pred,
                          [(i, e[0], e[1]) for i, e in enumerate(PR)])
    n = c['_母数']
    nok = sum(v for k, v in c.items() if k.endswith(' OK'))
    print('== %s  hyp=%s mode=%s  母数 %d（t=1 %d / t=2 %d）  当たり %d  外れ %d (%.0fs)'
          % (name, hyp.__name__, mode, n, c['_t=1'], c['_t=2'], nok, n - nok,
             time.time() - t0))
    for k in sorted(c, key=str):
        if not k.startswith('_'):
            print('   %-34s %d' % (k, c[k]))
    for k, e in list(ex.items())[:verbose]:
        S, B, t, r, r2, pred, pl = e
        print('   例 %s' % str(k))
        print('      A = %s' % show([list(x) for x in S]))
        print('      B = %s' % show([list(x) for x in B]))
        print("      t=%d r=%d  r'=%d 予測=%s" % (t, r, r2, pred))
        print('      PROV = %s' % pl)
    return c


# ---------------- 仮説 ----------------
def hyp_lastsh(S, PR, t, r, last):
    """末尾列が出した柱のうち、下から t 番目（sh0/sh1/body の並びの第 t-1）。"""
    pl = [i for i, e in enumerate(PR) if e[1] == last]
    return pl[t - 1] if 0 <= t - 1 < len(pl) else None


def hyp_kind(S, PR, t, r, last):
    """末尾列の `sh(t-1)` の柱。無ければ img r。"""
    kind = 'sh0' if t == 1 else ('sh1' if t == 2 else None)
    cand = [i for i, e in enumerate(PR) if e[1] == last and e[0] == kind]
    if cand:
        return cand[-1]
    bd = [i for i, e in enumerate(PR) if e[1] == r and e[0] == 'body']
    return bd[-1] if bd else None


def _anc0(B, x, k):
    """`B` の行 0 の親の鎖を `x` から `k` 段のぼった添字（`blockok` なら深さ -k）。"""
    P = pim(B)
    for _ in range(k):
        x = P[x][0]
        if x == -1:
            return None
    return x


def hyp_depth(S, PR, t, r, last):
    """`r'` = 末尾より行 0 が `d0` だけ浅い、直前でいちばん近い柱。"""
    B = hyp_depth.B
    d0 = S[last][0] - S[r][0]
    tgt = B[-1][0] - d0
    if tgt < 0:
        return None
    cand = [i for i in range(len(B) - 1) if B[i][0] == tgt]
    return cand[-1] if cand else None


def hyp_anc(S, PR, t, r, last):
    """`r'` = 末尾から行 0 の親の鎖を `d0` 段のぼった柱。"""
    B = hyp_anc.B
    d0 = S[last][0] - S[r][0]
    return _anc0(B, len(B) - 1, d0)


def steps_diag(pop, name, verbose=4):
    """`r'` に届くまでの行 0 の親の**段数**を `d0` と比べる。"""
    c = Counter(); ex = {}
    t0 = time.time()
    for n_, M in enumerate(pop):
        if n_ % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear()
            core._flat_memo.clear()
        S = tuple(map(tuple, M))
        br = badroot(S)
        if br is None:
            continue
        t, r = br
        B, PR = prov(S)
        B = tuple(map(tuple, B))
        br2 = badroot(B)
        if br2 is None:
            continue
        t2, r2 = br2
        last = len(S) - 1
        d0 = S[last][0] - S[r][0]
        d0p = B[-1][0] - B[r2][0]
        c['_母数'] += 1; c['_t=%d' % t] += 1
        c['t=%d  d0\'-d0 = %d' % (t, d0p - d0)] += 1
        if d0p != d0:
            # もとの A の側で、r と last のあいだの行 0 の祖先に
            # 「行 1 が末尾と同じ（タイ）」の柱があるか
            P = pim(S)
            x = last; ties = 0
            while True:
                x = P[x][0]
                if x == -1 or x <= r:
                    break
                if S[x][t] == S[last][t]:
                    ties += 1
            c['t=%d  d0\' != d0 のときの A 側のタイ数 %d' % (t, ties)] += 1
            k = (t, d0p - d0, ties)
            if k not in ex:
                ex[k] = (S, B, t, r, r2, d0, d0p)
    print('== %s  母数 %d（t=1 %d / t=2 %d）  (%.0fs)'
          % (name, c['_母数'], c['_t=1'], c['_t=2'], time.time() - t0))
    for k in sorted(c, key=str):
        if not k.startswith('_'):
            print('   %-44s %d' % (k, c[k]))
    for k, e in list(ex.items())[:verbose]:
        S, B, t, r, r2, d0, d0p = e
        print('   例 %s' % str(k))
        print('      A = %s' % show([list(x) for x in S]))
        print('      B = %s' % show([list(x) for x in B]))
        print("      t=%d r=%d d0=%d  r'=%d d0'=%d" % (t, r, d0, r2, d0p))
    return c


def tie_fit(pop, name, verbose=3):
    """仮説: t=1 のとき `d0' = d0 + 1` ⟺ `r` と末尾のあいだの行 0 の祖先に
    「行 1 が末尾と同じ」柱がある（＝ 行 1 のタイ）。2x2 で数える。"""
    c = Counter(); ex = {}
    t0 = time.time()
    for n_, M in enumerate(pop):
        if n_ % 20000 == 0:
            core._exp_memo.clear(); core._isstd_memo.clear()
            core._flat_memo.clear()
        S = tuple(map(tuple, M))
        br = badroot(S)
        if br is None:
            continue
        t, r = br
        B, PR = prov(S)
        B = tuple(map(tuple, B))
        br2 = badroot(B)
        if br2 is None:
            continue
        t2, r2 = br2
        last = len(S) - 1
        d0 = S[last][0] - S[r][0]
        d0p = B[-1][0] - B[r2][0]
        P = pim(S)
        x = last; tie = False
        while True:
            x = P[x][0]
            if x == -1 or x <= r:
                break
            if S[x][t] == S[last][t]:
                tie = True
        c['_母数'] += 1
        c['t=%d  tie=%s  d0\'-d0=%d' % (t, tie, d0p - d0)] += 1
        k = (t, tie, d0p - d0)
        if k not in ex:
            ex[k] = (S, B, t, r, r2, d0, d0p, tie)
    print('== %s  母数 %d  (%.0fs)' % (name, c['_母数'], time.time() - t0))
    for k in sorted(c, key=str):
        if not k.startswith('_'):
            print('   %-40s %d' % (k, c[k]))
    for k, e in list(ex.items())[:verbose]:
        S, B, t, r, r2, d0, d0p, tie = e
        if k[2] == 0 and k[1] is False:
            continue
        print('   例 %s' % str(k))
        print('      A = %s' % show([list(x) for x in S]))
        print('      B = %s' % show([list(x) for x in B]))
    return c


if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    what = sys.argv[2] if len(sys.argv) > 2 else 'explore'
    if lim == 0:      # 展開閉包
        import r3
        P = r3.pop_exp(6)
        lim = 'exp'
    else:
        P = sorted(gen3('BMS', lim, zcap=1), key=key)
    if what == 'explore':
        explore(P, 'gen3 <=%s' % lim)
    elif what == 'tie':
        tie_fit(P, 'gen3 <=%s' % lim)
    elif what == 'steps':
        steps_diag(P, 'gen3 <=%s' % lim)
    else:
        run(P, 'gen3 <=%s' % lim, globals()['hyp_' + what],
            sys.argv[3] if len(sys.argv) > 3 else 'real')
