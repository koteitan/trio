# -*- coding: utf-8 -*-
"""H11: 発火場所の素性表（h6feat.atoms 275 本 ＋ 条項ごとの追加）。"""
import sys, os, pickle
import os as _os
os.environ.setdefault('SBFLAGS', 'sibnb')
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3s
from rows3 import (par0, ANCHOR, is_branch, is_w_col, copy_head, term_top,
                   top_level, closes_unit, copy_src, is_diag, anch_before)
from h6feat import atoms, par, chain, descend_end, next_term

POS, NEG = pickle.load(open('/tmp/h1work/h11sites.pkl', 'rb'))
import os as _os
if _os.environ.get('H11ALL'):
    for t in _os.environ['H11ALL'].split(','):
        POS = list(POS) + list(pickle.load(open('/tmp/h1work/h11pos_%s.pkl' % t, 'rb')))
        NEG = list(NEG) + list(pickle.load(open('/tmp/h1work/h11neg_%s.pkl' % t, 'rb')))
    sp, sn = set(map(tuple, POS)), set(map(tuple, NEG))
    both = sp & sn
    print('正例 %d / 負例 %d / **矛盾（両方に出る場所）%d**'
          % (len(sp), len(sn), len(both)))
    POS = sorted(sp - both)
    NEG = sorted(sn - both)


def extra(Mo, off):
    n = len(Mo)
    p = tuple(Mo[off])
    a = {}
    a['x_anchor'] = (p == ANCHOR)
    a['x_z1'] = (p[2] == 1)
    a['x_v1'] = (p[1] == 1)
    a['x_v_ge2'] = (p[1] >= 2)
    a['x_diag'] = (p[0] == p[1])
    a['x_chead'] = copy_head(Mo, off)
    a['x_termtop'] = term_top(Mo, off)
    a['x_toplevel'] = top_level(Mo, off)
    a['x_par_root'] = (par0(Mo, off) == 0)
    a['x_cpysrc'] = (copy_src(Mo, off) is not None)
    a['x_isdiag'] = is_diag(Mo, off)
    nxt = Mo[off + 1] if off + 1 < n else None
    a['x_closes'] = closes_unit(nxt)
    a['x_last'] = (off == n - 1)
    a['x_anchbefore'] = anch_before(Mo, off)
    # 直前の柱が自分の親（= first）
    a['x_first'] = (off == 0 or par0(Mo, off) == off - 1)
    # 「兄」（自分の行 0 の親の 1 つ前の子）との関係
    q = par0(Mo, off)
    a['x_par_none'] = (q < 0)
    if q >= 0:
        a['x_par_anchor'] = (tuple(Mo[q]) == ANCHOR)
        a['x_par_z'] = (Mo[q][2] > 0)
        a['x_par_chead'] = copy_head(Mo, q)
        a['x_par_diag'] = (Mo[q][0] == Mo[q][1] and Mo[q][0] >= 1)
        a['x_par_dist1'] = (off - q == 1)
        a['x_par_r1_eq'] = (Mo[q][1] == p[1])
    else:
        for k in ('x_par_anchor', 'x_par_z', 'x_par_chead', 'x_par_diag',
                  'x_par_dist1', 'x_par_r1_eq'):
            a[k] = False
    # 直前の兄弟（同じ行 0）
    sib = None
    for t in range(off - 1, -1, -1):
        if Mo[t][0] < p[0]:
            break
        if Mo[t][0] == p[0]:
            sib = t
            break
    a['x_sib_none'] = (sib is None)
    if sib is not None:
        c = tuple(Mo[sib])
        a['x_sib_z'] = (c[2] > 0)
        a['x_sib_r1_eq'] = (c[1] == p[1])
        a['x_sib_r1_gt'] = (c[1] > p[1])
        a['x_sib_diag'] = (c[0] == c[1] and c[0] >= 1)
        a['x_sib_adj'] = (off - sib == 1)
        a['x_sib_anchor'] = (c == ANCHOR)
        a['x_sib_far'] = (off - sib > 3)
    else:
        for k in ('x_sib_z', 'x_sib_r1_eq', 'x_sib_r1_gt', 'x_sib_diag',
                  'x_sib_adj', 'x_sib_anchor', 'x_sib_far'):
            a[k] = False
    return a


X, Y, META, names = [], [], [], None
for lab, S in ((1, POS), (0, NEG)):
    for Mo, off in S:
        a = atoms(Mo, off)
        a.update(extra(Mo, off))
        if names is None:
            names = sorted(a)
        X.append(tuple(bool(a[nm]) for nm in names))
        Y.append(lab)
        META.append((Mo, off))
n = len(Y)
print('site %d 個  正例 %d / 負例 %d  素性 %d' % (n, sum(Y), n - sum(Y), len(names)))
pickle.dump((names, X, Y, META), open('/tmp/h1work/h11f%s.pkl' % _os.environ.get('H11ALL','').replace(',','_'), 'wb'))
res = []
for i, nm in enumerate(names):
    h = sum(1 for x, y in zip(X, Y) if x[i] == y)
    res.append((max(h, n - h), nm, h >= n - h))
res.sort(reverse=True)
print('--- 単一素性（最良 12）')
for h, nm, pol in res[:12]:
    print('   %-24s %s %d/%d' % (nm, '   ' if pol else 'not', h, n))
