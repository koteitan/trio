# -*- coding: utf-8 -*-
"""兄弟 site の素性と、正例／負例を分ける述語の総当たり。"""
import sys, pickle, itertools
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3sib
from rows3 import (is_branch, is_w_col, par0, hi_block, is_repeat, ANCHOR,
                   copy_head, term_top, top_level, closes_unit)

def lift_copy(Mo, j):
    """Mo[j:] の頭が、直前の同じ長さの区間の**持ち上げた写し**か。
    行 0 の差が一定 a>=1 で、行 1 の差は 0 か a、行 2 は同じ。"""
    n = len(Mo)
    for L in range(1, j + 1):
        if j + L > n:
            break
        ok = True; a = None
        for t in range(L):
            u, w = Mo[j - L + t], Mo[j + t]
            da = w[0] - u[0]
            if a is None: a = da
            if da != a or a < 1: ok = False; break
            if w[2] != u[2]: ok = False; break
            db = w[1] - u[1]
            if db not in (0, a): ok = False; break
        if ok:
            return L
    return 0

def atoms(Mo, off, site):
    n = len(Mo)
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else None
    p = tuple(Mo[off]); oB = site['oB']
    sb = g(oB); sb2 = g(oB + 1)
    q = par0(Mo, off); qc = g(q)
    a = {}
    a['lad0'] = bool(site['lad0'])
    a['lad1'] = bool(site['lad1'])
    a['dd_gt_d'] = site['dd'] > site['d']
    a['dd_d2'] = site['dd'] - site['d'] >= 2
    a['nA0'] = site['nA'] == 0
    a['v1'] = site['v'] == 1
    a['v_ge2'] = site['v'] >= 2
    a['s2_0'] = site['s2'] == 0
    a['z'] = p[2] > 0
    a['p_diag'] = p[0] == p[1] and p[0] >= 1
    a['p_anch'] = p == ANCHOR
    a['par_root'] = q == 0
    a['par_z'] = q >= 0 and Mo[q][2] > 0
    # 兄弟の頭
    a['sb_v0'] = sb is not None and sb[1] == 0
    a['sb_v1'] = sb is not None and sb[1] == 1
    a['sb_anch'] = sb is not None and tuple(sb) == ANCHOR
    a['sb_z'] = sb is not None and sb[2] > 0
    a['sb_w'] = sb is not None and is_w_col(sb)
    a['sb_br'] = sb is not None and is_branch(sb)
    a['sb_chead'] = sb is not None and copy_head(Mo, oB)
    a['sb_termtop'] = sb is not None and term_top(Mo, oB)
    a['sb_toplevel'] = sb is not None and top_level(Mo, oB)
    a['sb_lo'] = sb is not None and sb[0] < p[0]
    a['sb_eq'] = sb is not None and sb[0] == p[0]
    a['sb2_z'] = sb2 is not None and sb2[2] > 0
    a['sb2_deeper'] = sb2 is not None and sb2[0] > Mo[oB][0]
    # 写しの検出
    L = lift_copy(Mo, oB)
    a['sb_lift'] = L > 0
    a['sb_lift_full'] = L > 0 and oB + L == n
    a['sb_lift_ge2'] = L >= 2
    a['sb_lift_eqA'] = L == site['nA'] + 1
    a['sb_rep'] = is_repeat(Mo, oB + max(L,1) - 1) if L else False
    a['hi'] = hi_block(Mo, off)
    a['rep'] = is_repeat(Mo, off)
    a['anch_before'] = any(tuple(c) == ANCHOR for c in Mo[:off])
    a['anch_in_sib'] = any(tuple(c) == ANCHOR for c in Mo[oB:])
    a['chead_in_sib'] = any(copy_head(Mo, t) for t in range(oB, n))
    a['chead_before'] = any(copy_head(Mo, t) for t in range(0, oB))
    a['sib_last'] = oB + site['nB'] == n
    a['nB1'] = site['nB'] == 1
    a['off0'] = off == 0
    a['nA1'] = site['nA'] == 1
    a['nA_ge2'] = site['nA'] >= 2
    a['nA_ge3'] = site['nA'] >= 3
    a['nB_ge2'] = site['nB'] >= 2
    a['nB_ge4'] = site['nB'] >= 4
    a['nB_gt_nA'] = site['nB'] > site['nA']
    a['nB_eq_oB'] = site['nB'] == oB
    a['L_eq_oB'] = L == oB
    a['L_eq_nB'] = L == site['nB']
    a['L_ge2'] = L >= 2
    a['L_ge3'] = L >= 3
    a['L_gt_nA'] = L > site['nA'] + 1
    a['sib_desc'] = any(Mo[t][0] > p[0] for t in range(oB, n))
    a['ndep'] = len([1 for t in range(off) if Mo[t][0] < p[0]]) > 1
    a['p111'] = p == (1, 1, 1)
    a['p_z1'] = p[2] == 1
    a['tail_after_sib'] = oB + site['nB'] < n
    a['e1_gt_base'] = site['e1'] > site['base']
    a['e1_ge2'] = site['e1'] >= 2
    a['base_ge1'] = site['base'] >= 1
    a['A_has_w'] = any(is_w_col(Mo[t]) for t in range(off + 1, oB))
    a['A_has_z'] = any(Mo[t][2] > 0 for t in range(off + 1, oB))
    a['A_has_anch'] = any(tuple(Mo[t]) == ANCHOR for t in range(off + 1, oB))
    a['A_has_br'] = any(is_branch(Mo[t]) for t in range(off + 1, oB))
    a['A_has_chead'] = any(copy_head(Mo, t) for t in range(off + 1, oB))
    a['dd_eq_d1'] = site['dd'] == site['d'] + 1
    return a

def build():
    P, N = pickle.load(open('/tmp/h1work/sib_data.pkl','rb'))
    X, Y, META = [], [], []
    names = None
    # 正例: force に入った site
    for r in P:
        if r['kind'] != 'solved': continue
        smap = {s['off']: s for s in _sites(r['B'])}
        for o in r['force']:
            if o not in smap: continue
            a = atoms(r['B'], o, smap[o])
            if names is None: names = sorted(a)
            X.append(tuple(bool(a[k]) for k in names)); Y.append(True)
            META.append(('pos', r['A'], r['m'], o))
    # 負例: シートで壊れる site
    for r in N:
        if not r['broke']: continue
        a = atoms(r['B'], r['off'], r['site'])
        X.append(tuple(bool(a[k]) for k in names)); Y.append(False)
        META.append(('sheet', r['row'], None, r['off']))
    return names, X, Y, META

def _sites(B):
    rows3sib.SIBMODE[0]=2
    rows3sib.SIBREC[0]=True; del rows3sib.SIBSITES[:]
    rows3sib.SIBFORCE.clear()
    rows3sib.b2d3(list(B))
    rows3sib.SIBREC[0]=False
    out, seen = [], set()
    for s in rows3sib.SIBSITES:
        if s['off'] in seen: continue
        seen.add(s['off']); out.append(s)
    return out

if __name__ == '__main__':
    names, X, Y, M = build()
    n=len(Y); print('site %d 個（正 %d / 負 %d）  素性 %d' % (n, sum(Y), n-sum(Y), len(names)))
    res=[]
    for i,nm in enumerate(names):
        h=sum(1 for x,y in zip(X,Y) if x[i]==y)
        res.append((max(h,n-h), nm, h>=n-h, h))
    res.sort(reverse=True)
    print('--- 単一素性（最良 15）')
    for h,nm,pol,_ in res[:15]:
        print('   %-16s %s  %d/%d' % (nm, '   ' if pol else 'not', h, n))
    pickle.dump((names,X,Y,M), open('/tmp/h1work/sib_feat.pkl','wb'))
