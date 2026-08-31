# -*- coding: utf-8 -*-
"""prev==0 の枝（誤り 525 本）を分ける述語を総当たりで探す。"""
import sys, itertools
from collections import Counter, defaultdict
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3
from rows3 import (is_branch, is_w_col, closes_unit, par0, hi_block,
                   is_repeat, wchain_head, ANCHOR)
from h1an import load


def uh_at(Mo, off):
    for j in range(off, -1, -1):
        c = Mo[j]
        if c[0] == 0 or (c[1] == 0 and c[2] == 0) or tuple(c) == ANCHOR:
            return j
    return 0


def atoms(Mo, off, dec):
    n = len(Mo)
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else None
    p = tuple(Mo[off]); p0 = p[0]
    onx = g(off + 1); onx2 = g(off + 2)
    nxt = dec['nxt']
    pv, pv2, pv3 = g(off-1), g(off-2), g(off-3)
    q = par0(Mo, off); qc = g(q)
    wj = wchain_head(Mo, off)
    uh = uh_at(Mo, off)
    a = {}
    N = lambda c: c if c is not None else (-1, -1, -1)
    x = N(onx); y = N(nxt)
    a['onx_ge'] = onx is not None and onx[0] >= p0
    a['onx_gt'] = onx is not None and onx[0] > p0
    a['onx_eq'] = onx is not None and onx[0] == p0
    a['onx_lt1'] = onx is not None and onx[0] == p0 - 1
    a['nxt_ge'] = nxt is not None and nxt[0] >= p0
    a['nxt_br'] = nxt is not None and is_branch(nxt)
    a['onx_br'] = onx is not None and is_branch(onx)
    a['onx_v0'] = onx is not None and onx[1] == 0
    a['onx_v1'] = onx is not None and onx[1] == 1
    a['onx_vge'] = onx is not None and onx[1] >= 1
    a['onx_z'] = onx is not None and onx[2] > 0
    a['onx_w'] = onx is not None and is_w_col(onx)
    a['onx_none'] = onx is None
    a['onx_anch'] = onx is not None and tuple(onx) == ANCHOR
    a['closes'] = closes_unit(nxt)
    a['ocloses'] = closes_unit(onx)
    a['onx2_ge'] = onx2 is not None and onx2[0] >= p0
    a['onx2_z'] = onx2 is not None and onx2[2] > 0
    a['onx2_w'] = onx2 is not None and is_w_col(onx2)
    a['onx2_none'] = onx2 is None
    # 直前
    a['pv_br'] = pv is not None and is_branch(pv)
    a['pv_w'] = pv is not None and is_w_col(pv)
    a['pv_z'] = pv is not None and pv[2] > 0
    a['pv_v0'] = pv is not None and pv[1] == 0
    a['pv_lo'] = pv is not None and pv[0] == p0 - 1
    a['pv_eq'] = pv is not None and pv[0] == p0
    a['pv_anch1'] = pv is not None and tuple(pv) == (p0 - 1, 1, 1)
    a['pv2_w'] = pv2 is not None and is_w_col(pv2)
    a['pv2_z'] = pv2 is not None and pv2[2] > 0
    a['pv2_br'] = pv2 is not None and is_branch(pv2)
    # 自分・文脈
    a['hi'] = hi_block(Mo, off)
    a['rep'] = is_repeat(Mo, off)
    a['par_w'] = q >= 0 and is_w_col(Mo[q])
    a['par_z'] = q >= 0 and Mo[q][2] > 0
    a['par_root'] = q == 0
    a['par_anch'] = q >= 0 and tuple(Mo[q]) == ANCHOR
    a['par_anch1'] = q >= 0 and Mo[q][1] >= 1 and Mo[q][2] >= 1
    a['par_br'] = q >= 0 and is_branch(Mo[q])
    a['wch'] = wj is not None
    a['wch_root'] = wj is not None and par0(Mo, wj) == 0
    a['wch_deep'] = wj is not None and not (par0(Mo, wj) == 0)
    a['uh_w'] = is_w_col(Mo[uh])
    a['uh_anch'] = tuple(Mo[uh]) == ANCHOR
    a['uh_root'] = Mo[uh][0] == 0
    a['uh_adj'] = off - uh == 1
    a['nbr0'] = sum(1 for t in range(uh, off) if is_branch(Mo[t])) == 0
    a['nbr1'] = sum(1 for t in range(uh, off) if is_branch(Mo[t])) == 1
    a['nw0'] = sum(1 for t in range(uh, off) if is_w_col(Mo[t])) == 0
    a['anch_before'] = any(tuple(c) == ANCHOR for c in Mo[:off])
    a['w_before'] = any(is_w_col(c) for c in Mo[:off])
    a['z_before'] = any(c[2] > 0 for c in Mo[:off])
    a['z_after'] = any(c[2] > 0 for c in Mo[off+1:])
    a['p0_ge3'] = p0 >= 3
    a['p0_ge4'] = p0 >= 4
    a['last'] = off == n - 1
    return a


def collect(whyset=('prev0/shallow', 'prev0/deep')):
    R = load('S.pkl','T5.pkl','T6.pkl','T6_6.pkl')
    tab, cur, dec, src = {}, {}, {}, defaultdict(set)
    for r in R:
        k = (r['A'], r['off'])
        tab[k] = r['shallow']; cur[k] = r['dec']['shallow']; dec[k] = r['dec']
        src[k].add(r['src'])
    out = []
    for k in tab:
        if dec[k]['why'] not in whyset:
            continue
        out.append((k[0], k[1], tab[k], cur[k], dec[k], sorted(src[k])))
    return out


if __name__ == '__main__':
    D = collect()
    print('prev0 の枝（上書きなし）%d 本  正解 浅い %d / 深い %d'
          % (len(D), sum(1 for d in D if d[2]), sum(1 for d in D if not d[2])))
    NAMES = sorted(atoms(D[0][0], D[0][1], D[0][4]))
    X = [tuple(bool(atoms(A,off,dec)[nm]) for nm in NAMES) for A,off,lab,cur,dec,s in D]
    Y = [not d[2] for d in D]      # True = 深いのが正しい
    n = len(Y)
    print('素性 %d 個  目標(深い) %d 本' % (len(NAMES), sum(Y)))
    res = []
    for i, nm in enumerate(NAMES):
        h = sum(1 for x,y in zip(X,Y) if x[i]==y)
        res.append((max(h,n-h), nm, h>=n-h, h))
    res.sort(reverse=True)
    print('--- 単一素性（最良 15）')
    for h,nm,pol,_ in res[:15]:
        print('   %-12s %s  %d/%d  (外し %d)' % (nm, '   ' if pol else 'not', h, n, n-h))
    import pickle
    pickle.dump((NAMES, X, Y, [(d[0],d[1],d[5]) for d in D]), open('/tmp/h1work/P0.pkl','wb'))
