# -*- coding: utf-8 -*-
"""H11 (1): ImgClosedT の破れ 54 個で、ずれた柱の first / ps / split0 / d / dd。

目標 T = (conv3 A)<m>、答え C = conv3(A<n>)（T にいちばん長く合う n）。
k = lcp(C,T) が**最初にずれた柱**。PROV から出どころ off を引き、
LREC から first / ps / d / nA を引く。写し a-1 の対応する柱 off-bp とも比べる。
"""
import sys, pickle
from collections import Counter
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools/g2')
import rows3, rows3F, provc
from rows3 import is_branch, par0
from h10L3 import seg
from h11m import first_mat, ps_mat, nA_mat
from core import expand, show


def lcp(a, b):
    i, n = 0, min(len(a), len(b))
    while i < n and a[i] == b[i]:
        i += 1
    return i


def rec_at(rec, off):
    for R in rec:
        if R['off'] == off:
            return R
    return None


def run():
    bad = sorted(pickle.load(open('/tmp/h1work/img54p.pkl', 'rb')),
                 key=lambda e: (len(e[0]), e[0], e[1]))
    rows = []
    for A, m, T in bad:
        S = tuple(map(tuple, A))
        T = tuple(map(tuple, T))
        sg = seg(S)
        best = None
        exact = None
        for n in range(1, 10):
            E = [tuple(x) for x in expand(S, n)]
            if not E:
                continue
            C, PR = provc.b2d3p(list(E))
            k = lcp(C, T)
            if best is None or k > best[0]:
                best = (k, n, tuple(E), C, PR)
            if len(C) == len(T) and exact is None:
                exact = (k, n, tuple(E), C, PR)
            if len(C) > len(T) + 4:
                break
        # 長さが合う n を優先する（合わないと柱ごとに整列できない）
        k, n, E, C, PR = exact if exact is not None else best
        e0 = dict(exact=exact is not None)
        e = dict(A=S, m=m, T=T, n=n, E=E, C=C, k=k, seg=sg, **e0)
        if k >= len(PR):
            e['tag'] = 'ずれが記録の外（像が短い）'
            rows.append(e)
            continue
        kind, off, why, ctx = PR[k]
        e.update(kind=kind, off=off, why=why, ctx=ctx,
                 want=T[k] if k < len(T) else None, got=C[k])
        out, rec = rows3F.b2d3F(list(E))
        R = rec_at(rec, off)
        e['R'] = R
        e['col'] = E[off]
        e['isbr'] = is_branch(E[off])
        e['fm'] = first_mat(E, off)
        e['pm'] = ps_mat(E, off)
        e['nm'] = nA_mat(E, off)
        if sg is not None:
            r, bp, delta, t = sg
            e['bp'] = bp
            e['cpy'] = (off - r) // bp if off >= r else -1
            j = off - bp
            e['R0'] = rec_at(rec, j) if j >= 0 else None
            e['col0'] = E[j] if 0 <= j < len(E) else None
            e['fm0'] = first_mat(E, j) if j >= 0 else None
            e['nm0'] = nA_mat(E, j) if j >= 0 else None
        e['tag'] = 'ok'
        rows.append(e)
    return rows


if __name__ == '__main__':
    rows = run()
    pickle.dump(rows, open('/tmp/h1work/h11rows.pkl', 'wb'))
    c = Counter(r['tag'] for r in rows)
    print('破れ %d 個: %s' % (len(rows), dict(c)))
    ok = [r for r in rows if r['tag'] == 'ok']
    print()
    print('ずれた柱の型:')
    print('   分岐列 (a,1,0)      %d' % sum(1 for r in ok if r['isbr']))
    print('   分岐列でない        %d' % sum(1 for r in ok if not r['isbr']))
    print('   柱の型の内訳: %s' % Counter(
        ('branch' if r['isbr'] else str(r['col'])) for r in ok).most_common(10))
    print()
    print('kind（像のどの柱でずれたか）: %s'
          % Counter(r['kind'] for r in ok).most_common())
    print('why:  %s' % Counter(str(r['why']) for r in ok).most_common())
    print('ctx:  %s' % Counter(str(r['ctx']) for r in ok).most_common())
    print()
    print('深さのずれ  want[0]-got[0]: %s'
          % Counter(r['want'][0] - r['got'][0] for r in ok
                    if r['want']).most_common())
    print('綴りのずれ  (want, got) の型: %s'
          % Counter(('同深さ' if r['want'] and r['want'][0] == r['got'][0]
                     else '深さ') for r in ok if r['want']).most_common())
    print()
    print('first / ps / nA が写し a-1 とちがうか:')
    cc = Counter()
    for r in ok:
        if 'R0' not in r or r['R'] is None or r['R0'] is None:
            cc['対応が取れない'] += 1
            continue
        b = []
        if r['R']['first'] != r['R0']['first']:
            b.append('first')
        if r['R']['ps'] != r['R0']['ps']:
            b.append('ps')
        if r['R']['nA'] != r['R0']['nA']:
            b.append('nA')
        cc[tuple(b) or ('同じ',)] += 1
    for k, v in cc.most_common():
        print('   %-28s %d' % (str(k), v))
    print()
    print('conv3 の first/ps/nA と 行列読み first_mat/ps_mat/nA_mat の差:')
    cc = Counter()
    for r in ok:
        if r['R'] is None:
            cc['記録なし'] += 1
            continue
        b = []
        if r['R']['first'] != r['fm']:
            b.append('first')
        if r['R']['first'] and r['R']['ps'] != r['pm']:
            b.append('ps')
        if r['R']['nA'] != r['nm']:
            b.append('nA')
        cc[tuple(b) or ('全部一致',)] += 1
    for k, v in cc.most_common():
        print('   %-28s %d' % (str(k), v))
