# -*- coding: utf-8 -*-
"""縮約の cB site の素性表。"""
import sys, pickle
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3
from rows3 import (is_branch, is_w_col, par0, hi_block, is_repeat, ANCHOR,
                   copy_head, term_top, top_level, closes_unit)

def atoms(Mo, off, s):
    n = len(Mo)
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else None
    p = tuple(Mo[off]); oBq = s['oBq']
    sb = g(oBq); sb2 = g(oBq + 1)
    q = par0(Mo, off)
    a = {}
    for k in ('lad0','lad1','deep_end'):
        a[k] = bool(s[k])
    a['e1flag'] = s['e'] == 1
    a['e0flag'] = s['e'] == 0
    a['v1'] = s['v'] == 1
    a['v_ge2'] = s['v'] >= 2
    a['s2_0'] = s['s2'] == 0
    a['s2_1'] = s['s2'] == 1
    a['nA0'] = s['nA'] == 0
    a['nA1'] = s['nA'] == 1
    a['nA_ge2'] = s['nA'] >= 2
    a['nU0'] = s['nU'] == 0
    a['nU_ge2'] = s['nU'] >= 2
    a['nR0'] = s['nR'] == 0
    a['nR1'] = s['nR'] == 1
    a['nR_ge2'] = s['nR'] >= 2
    a['nBq1'] = s['nBq'] == 1
    a['nBq_ge2'] = s['nBq'] >= 2
    a['dd_d1'] = s['dd'] - s['d'] == 1
    a['dd_d2'] = s['dd'] - s['d'] >= 2
    a['rd_gt_d1'] = s['rd'] > s['d'] + 1
    a['rd_eq_d1'] = s['rd'] == s['d'] + 1
    a['d0'] = s['d'] == 0
    a['d1'] = s['d'] == 1
    a['e1_gt_base'] = s['e1'] > s['base']
    # 行列から
    a['p_z'] = p[2] > 0
    a['p_diag'] = p[0] == p[1] and p[0] >= 1
    a['p_anch'] = p == ANCHOR
    a['p_root'] = p[0] == 0
    a['par_root'] = q == 0
    a['par_z'] = q >= 0 and Mo[q][2] > 0
    a['sb_v0'] = sb is not None and sb[1] == 0
    a['sb_w'] = sb is not None and is_w_col(sb)
    a['sb_chead'] = sb is not None and copy_head(Mo, oBq)
    a['sb_termtop'] = sb is not None and term_top(Mo, oBq)
    a['sb_anch'] = sb is not None and tuple(sb) == ANCHOR
    a['sb_br'] = sb is not None and is_branch(sb)
    a['sb_z'] = sb is not None and sb[2] > 0
    a['sb_root'] = sb is not None and sb[0] == 0
    a['sb_eqp'] = sb is not None and sb[0] == p[0]
    a['sb_lo'] = sb is not None and sb[0] < p[0]
    a['sb2_none'] = sb2 is None
    a['sb2_deeper'] = sb2 is not None and sb2[0] > sb[0]
    a['sb_last'] = oBq == n - 1
    a['tail1'] = n - oBq == 1
    a['tail_ge3'] = n - oBq >= 3
    a['hi'] = hi_block(Mo, off)
    a['rep'] = is_repeat(Mo, off)
    a['anch_before'] = any(tuple(c) == ANCHOR for c in Mo[:off])
    a['chead_any'] = any(copy_head(Mo, t) for t in range(n))
    a['A_has_w'] = any(is_w_col(Mo[t]) for t in range(off + 1, oBq))
    a['A_has_z'] = any(Mo[t][2] > 0 for t in range(off + 1, oBq))
    a['off0'] = off == 0
    return {k: bool(v) for k, v in a.items()}

def build(lim=7):
    P, N = pickle.load(open('/tmp/h1work/cb_data%d.pkl'%lim,'rb'))
    X, Y, META, names = [], [], [], None
    for r, lab in [(x, True) for x in P] + [(x, False) for x in N]:
        a = atoms(r['B'], r['off'], r['site'])
        if names is None: names = sorted(a)
        X.append(tuple(a[k] for k in names)); Y.append(lab)
        META.append((r['B'], r['off']))
    return names, X, Y, META

if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv)>1 else 7
    names, X, Y, M = build(lim)
    n=len(Y)
    print('site %d 個（正 %d / 負 %d）  素性 %d' % (n, sum(Y), n-sum(Y), len(names)))
    pickle.dump((names,X,Y,M), open('/tmp/h1work/cb_feat.pkl','wb'))
    res=[]
    for i,nm in enumerate(names):
        h=sum(1 for x,y in zip(X,Y) if x[i]==y)
        res.append((max(h,n-h), nm, h>=n-h))
    res.sort(reverse=True)
    print('--- 単一素性（最良 12）')
    for h,nm,pol in res[:12]: print('   %-14s %s %d/%d' % (nm,'   ' if pol else 'not',h,n))
