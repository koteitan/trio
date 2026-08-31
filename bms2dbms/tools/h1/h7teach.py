# -*- coding: utf-8 -*-
"""H7 (2): 教師データを「長さで対応づける」形に広げる。

いままでは `T = (conv3 A)<m>` と `E = A<m+1>` という**固定のずらし**で対にしていた。
そのせいで n = m の対（`conv3(A<n>) = (conv3 A)<n>`）が丸ごと落ちていた。
ここでは A ごとに `(conv3 A)<m>` を全部作り、`conv3(A<n>)` と**長さが一致する m**
を探して対にする。
"""
import sys, pickle, time
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, provh
from rows3 import is_branch
from core import expand

def collect(lim=6, nmax=4, mmax=8, zcap=1, f=None, prov=None, verbose=1):
    f = f or rows3.b2d3
    prov = prov or provh.b2d3p
    A = sorted(rows3.gen3('BMS', lim, zcap=zcap), key=rows3.key)
    rows = []; c = Counter(); t0 = time.time()
    for i, M in enumerate(A):
        if len(M) < 2: continue
        Mt = tuple(map(tuple, M))
        fM = tuple(map(tuple, f(list(M))))
        byl = {}
        for m in range(1, mmax + 1):
            T = tuple(expand(fM, m))
            byl.setdefault(len(T), []).append((m, T))
        for n in range(1, nmax + 1):
            E = tuple(tuple(x) for x in expand(Mt, n))
            U, pr = prov(list(E))
            cand = byl.get(len(U))
            if not cand:
                c['長さの合う m が無い'] += 1; continue
            # lcp が最大の m を採る（同点なら m が小さいほう）
            from imgfast import lcp
            m, T = max(cand, key=lambda mt: (lcp(U, mt[1]), -mt[0]))
            if lcp(U, T) * 2 < len(U):
                c['lcp が短い（捨てる）'] += 1; continue
            c['対 (n=%d,m=%d)' % (n, m) if n != m else '対 (n=m=%d)' % n] += 1
            c['**ずれ %+d**' % (m - n)] += 1
            for q, w, pe in zip(U, T, pr):
                k, off, why, d = pe[0], pe[1], pe[2], pe[4]
                if k != 'body' or d is None or d.get('why') == 'tie': continue
                if not is_branch(E[off]): continue
                wv = w[1]
                if wv == d['base_s'] and wv != d['deep']: lab = True
                elif wv == d['deep'] and wv != d['base_s']: lab = False
                else: c['ラベルが決まらない'] += 1; continue
                rows.append(dict(A=E, off=off, n=n, m=m, shallow=lab,
                                 got=d['shallow'], dec=d, want=tuple(w),
                                 src=(Mt, n)))
        if verbose and (i+1) % 2000 == 0:
            print('  %d/%d  柱 %d  %.0fs' % (i+1, len(A), len(rows), time.time()-t0), flush=True)
    return rows, c

if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv)>1 else 6
    nm  = int(sys.argv[2]) if len(sys.argv)>2 else 4
    rows, c = collect(lim, nm)
    print('ラベル付き柱 %d 本' % len(rows))
    for k in sorted(c, key=str):
        if k.startswith('**') or 'm が' in k or 'ラベル' in k: print('   %-24s %d' % (k, c[k]))
    err = [r for r in rows if r['got'] != r['shallow']]
    print('いまの conv3 の誤り %d 本   内訳:' % len(err),
          dict(Counter(r['dec']['why'] for r in err)))
    pickle.dump(rows, open('/tmp/h1work/W%d_%d.pkl' % (lim, nm), 'wb'))
