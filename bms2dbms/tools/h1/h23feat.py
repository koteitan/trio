# -*- coding: utf-8 -*-
"""H23: 単調な素性だけを使う教師データ（課題 H22 の教訓）。

**反単調な素性を最初から外す**:
  行列の末尾を読むもの      last_* / x_last / tail1 / tail2 / desc_end / nt_end
  「後ろに〜が無い」        *_after0 / *0 （chead_after0 / z_after0 / nth0 / after_unit0）
  次の柱を**そのまま**読む  nx1_* / nx2_* / nx3_* / x_closes / f*_none
  「子が無い」              desc0
"""
import sys, os, pickle
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3v, sheet3
from h6feat import atoms
from h11feat import extra
from h13x import far

BAD_PREFIX = ('nx1_', 'nx2_', 'nx3_', 'last_')
BAD_EXACT = {'x_last', 'x_closes', 'tail1', 'tail2', 'desc_end', 'desc0',
             'nt_end', 'nt1', 'nt2', 'z_after0', 'z_after1', 'chead_after0',
             'chead_after1', 'nchead0', 'nchead1', 'nth0', 'nth1',
             'after_unit0', 'f1_none', 'f2_none', 'f3_none', 'in_blk_tail',
             'z_next_adj', 'x_sib_none', 'pv1_none', 'pv2_none', 'pv3_none'}


def ok(nm):
    return not nm.startswith(BAD_PREFIX) and nm not in BAD_EXACT


def vec(Mo, off):
    a = atoms(Mo, off)
    a.update(extra(Mo, off))
    a.update(far(Mo, off))
    return {k: v for k, v in a.items() if ok(k)}


if __name__ == '__main__':
    FIX = pickle.load(open('/tmp/h1work/h14fix.pkl', 'rb'))
    POS = {'D': set(), 'E': set()}
    for Bt, off, val in FIX:
        POS['E' if val == 'sd' else 'D'].append((Bt, off)) if False else \
            POS['E' if val == 'sd' else 'D'].add((Bt, off))
    NEG = {'D': set(), 'E': set()}
    n = 0
    for row, b, d in sheet3.load(1):
        E = tuple(map(tuple, b))
        o0, S = rows3v.b2d3v(list(E))
        if o0 != tuple(map(tuple, d)):
            continue
        n += 1
        for off, sh, bs, dp, bsd, tie in S:
            if tie:
                if bsd != dp and rows3v.b2d3v(list(E), {off: 'sd'})[0] != o0:
                    NEG['E'].add((E, off))
            elif sh:
                if rows3v.b2d3v(list(E), {off: False})[0] != o0:
                    NEG['D'].add((E, off))
    print('シート %d 行' % n)
    for t in os.environ.get('ADD', '').split(','):
        if t.strip():
            for cls in 'DE':
                f = '/tmp/h1work/h23neg_%s_%s.pkl' % (cls, t.strip())
                if os.path.exists(f):
                    NEG[cls] |= set(tuple(x) for x in pickle.load(open(f, 'rb')))
    for cls in 'DE':
        both = POS[cls] & NEG[cls]
        P, N = sorted(POS[cls] - both), sorted(NEG[cls])
        print('クラス %s: 正例 %d / 負例 %d / ぶつかり %d' % (cls, len(P), len(N), len(both)))
        if not P:
            continue
        X, Y, META, names = [], [], [], None
        for lab, S2 in ((1, P), (0, N)):
            for Mo, off in S2:
                a = vec(Mo, off)
                if names is None:
                    names = sorted(a)
                X.append(tuple(bool(a[nm]) for nm in names))
                Y.append(lab)
                META.append((Mo, off))
        nx = {}
        for i, y in enumerate(Y):
            if not y:
                nx.setdefault(X[i], []).append(i)
        coll = sum(1 for i, y in enumerate(Y) if y and X[i] in nx)
        print('   単調な素性 %d / **完全一致する正例 %d**' % (len(names), coll))
        pickle.dump((names, X, Y, META), open('/tmp/h1work/h23f%s.pkl' % cls, 'wb'))
