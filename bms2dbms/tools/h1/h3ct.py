# -*- coding: utf-8 -*-
"""closes_top の撃ちすぎ 36 本を分ける述語を教師データから探す。"""
import sys, pickle, time
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3
from rows3 import (is_branch, is_w_col, closes_unit, par0, hi_block, is_repeat,
                   wchain_head, ANCHOR, copy_head, term_top, top_level, closes_top)

def uh_at(Mo, off):
    for j in range(off, -1, -1):
        c = Mo[j]
        if c[0] == 0 or (c[1] == 0 and c[2] == 0) or tuple(c) == ANCHOR:
            return j
    return 0

def chain_len(Mo, j):
    """写しの頭 j から根まで、いくつ (k,0,0) を経由するか。"""
    n = 0
    while True:
        q = par0(Mo, j)
        if q < 0: return n
        if Mo[q][0] == 0: return n + 1
        n += 1; j = q
        if n > 64: return n

def atoms(Mo, off, dec):
    n = len(Mo)
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else None
    p = tuple(Mo[off]); p0 = p[0]
    j = off + 1
    nx = g(j); nx2 = g(j + 1); nx3 = g(j + 2)
    pv, pv2 = g(off - 1), g(off - 2)
    q = par0(Mo, off); qn = par0(Mo, j)
    uh = uh_at(Mo, off); wj = wchain_head(Mo, off)
    a = {}
    a['nx_w'] = nx is not None and is_w_col(nx)
    a['nx_chead'] = nx is not None and copy_head(Mo, j)
    a['nx_lt'] = nx is not None and nx[0] < p0
    a['nx_lt2'] = nx is not None and nx[0] <= p0 - 2
    a['nx_ge'] = nx is not None and nx[0] >= p0
    a['nx_v1'] = nx is not None and nx[1] == 1
    a['nx_last'] = j == n - 1
    a['nx2_none'] = nx2 is None
    a['nx2_z'] = nx2 is not None and nx2[2] > 0
    a['nx2_anch'] = nx2 is not None and nx2[1] >= 1 and nx2[2] >= 1
    a['nx2_deeper'] = nx2 is not None and nx2[0] > nx[0]
    a['nx3_none'] = nx3 is None
    a['npar_root'] = qn == 0
    a['npar_chead'] = qn >= 0 and copy_head(Mo, qn)
    a['npar_anch'] = qn >= 0 and tuple(Mo[qn]) == ANCHOR
    a['npar_far'] = qn >= 0 and j - qn > 4
    a['chain1'] = chain_len(Mo, j) == 1
    a['chain2'] = chain_len(Mo, j) == 2
    a['chain_ge3'] = chain_len(Mo, j) >= 3
    a['pv_br'] = pv is not None and is_branch(pv)
    a['pv_z'] = pv is not None and pv[2] > 0
    a['pv_w'] = pv is not None and is_w_col(pv)
    a['pv_lo'] = pv is not None and pv[0] == p0 - 1
    a['pv_eq'] = pv is not None and pv[0] == p0
    a['pv2_z'] = pv2 is not None and pv2[2] > 0
    a['hi'] = hi_block(Mo, off)
    a['rep'] = is_repeat(Mo, off)
    a['par_root'] = q == 0
    a['par_z'] = q >= 0 and Mo[q][2] > 0
    a['par_chead'] = q >= 0 and copy_head(Mo, q)
    a['par_anch'] = q >= 0 and tuple(Mo[q]) == ANCHOR
    a['wch'] = wj is not None
    a['uh_w'] = is_w_col(Mo[uh])
    a['uh_anch'] = tuple(Mo[uh]) == ANCHOR
    a['uh_root'] = Mo[uh][0] == 0
    a['uh_far'] = off - uh > 2
    a['nbr0'] = sum(1 for t in range(uh, off) if is_branch(Mo[t])) == 0
    a['anch_before'] = any(tuple(c) == ANCHOR for c in Mo[:off])
    a['chead_before'] = any(copy_head(Mo, t) for t in range(0, j))
    a['nchead1'] = sum(1 for t in range(0, n) if copy_head(Mo, t)) == 1
    a['nchead_ge3'] = sum(1 for t in range(0, n) if copy_head(Mo, t)) >= 3
    a['z_after'] = any(c[2] > 0 for c in Mo[j:])
    a['p0_ge4'] = p0 >= 4
    a['p_prev0'] = dec['prev0'] == 0
    a['p_prev1'] = dec['prev0'] == 1
    a['tail'] = n - j
    a['tail1'] = n - j == 1
    a['tail_ge5'] = n - j >= 5
    nch = [t for t in range(n) if copy_head(Mo, t)]
    after = [t for t in nch if t > j]
    a['ch_after0'] = len(after) == 0
    a['ch_after1'] = len(after) == 1
    a['ch_after_ge2'] = len(after) >= 2
    before = [t for t in nch if t < j]
    a['ch_before0'] = len(before) == 0
    a['ch_before1'] = len(before) == 1
    a['ch_before2'] = len(before) == 2
    a['ch_before_ge3'] = len(before) >= 3
    a['ch_idx_last'] = bool(nch) and j == nch[-1]
    a['ch_idx_first'] = bool(nch) and j == nch[0]
    a['blk'] = (nch[1] - nch[0]) if len(nch) >= 2 else 0
    a['blk_eq_tail'] = len(nch) >= 2 and (n - j) == (nch[1] - nch[0])
    a['off_in_blk_last'] = bool(nch) and off + 1 in nch
    a['ntail_blk'] = len(nch) >= 2 and (n - j) // max(1, nch[1] - nch[0]) == 1
    return {k: bool(v) for k, v in a.items()}

def build():
    tab, cur, dec = pickle.load(open('/tmp/h1work/h2tab.pkl','rb'))
    X, Y, META, names = [], [], [], None
    for k in tab:
        A, off = k
        d = dec[k]
        if d.get('shallow') is None: continue
        nxt = d['nxt']
        if closes_unit(nxt): continue
        if off + 1 >= len(A): continue
        if not closes_top(A, off, nxt): continue
        a = atoms(A, off, d)
        if names is None: names = sorted(a)
        X.append(tuple(a[nm] for nm in names))
        Y.append(not tab[k])        # True = 正解は深い（closes_top を止めるべき）
        META.append(k)
    return names, X, Y, META

if __name__ == '__main__':
    names, X, Y, M = build()
    n = len(Y)
    print('closes_top が新しく発火する site %d 個   止めるべき %d / このままで正しい %d'
          % (n, sum(Y), n - sum(Y)))
    pickle.dump((names, X, Y, M), open('/tmp/h1work/ct_feat.pkl','wb'))
    res = []
    for i, nm in enumerate(names):
        h = sum(1 for x, y in zip(X, Y) if x[i] == y)
        res.append((max(h, n-h), nm, h >= n-h))
    res.sort(reverse=True)
    print('--- 単一素性（最良 12）')
    for h, nm, pol in res[:12]:
        print('   %-14s %s %d/%d' % (nm, '   ' if pol else 'not', h, n))
