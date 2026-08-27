# -*- coding: utf-8 -*-
"""族 β: 破れた (A,m) について逆写像 d2b3 が返す B を教師にする。
   |conv3(B)| == |T| なら柱ごとに整列できる。"""
import sys, time
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, provh, inv3, imgfast
from core import expand, isstd, show

def failing(lim=5, mmax=3, jobs=4):
    A = sorted(rows3.gen3('BMS', lim, zcap=1), key=rows3.key)
    ok, tot, bad = imgfast.imgclosed_fast(rows3.b2d3, A, mmax, inv3.d2b3, jobs=jobs)
    return sorted(bad, key=rows3.key)

def probe(M, mmax=3):
    fM = tuple(map(tuple, rows3.b2d3(list(M))))
    out = []
    for m in range(1, mmax+1):
        T = tuple(expand(fM, m))
        try:
            B = inv3.d2b3(T)
        except Exception:
            B = None
        rec = dict(m=m, T=T, B=(tuple(map(tuple,B)) if B else None))
        if B:
            rec['std'] = isstd(B, 'BMS') and all(c[2] <= 1 for c in B)
            try:
                Q, pr = provh.b2d3p(list(B))
            except Exception:
                Q, pr = None, None
            rec['Q'] = Q; rec['pr'] = pr
            if Q is not None:
                rec['same_len'] = (len(Q) == len(T))
                rec['diff'] = [i for i in range(min(len(Q), len(T))) if tuple(Q[i]) != tuple(T[i])]
        out.append(rec)
    return out

if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv)>1 else 5
    mm  = int(sys.argv[2]) if len(sys.argv)>2 else 3
    t0=time.time()
    F = failing(lim, mm)
    print('破れた A %d 個 (lim=%d, m<=%d)  %.0fs' % (len(F), lim, mm, time.time()-t0), flush=True)
    c = Counter()
    for M in F:
        rs = probe(M, mm)
        for r in rs:
            if r['B'] is None: c['B なし']+=1; continue
            if not r.get('std'): c['B が非標準']+=1; continue
            if r.get('Q') is None: c['像が取れない']+=1; continue
            if r['Q']==r['T']: c['一致（この m は破れていない）']+=1; continue
            if r.get('same_len'): c['同長 ちがい %d 本'%len(r['diff'])]+=1
            else: c['長さちがい %+d'%(len(r['Q'])-len(r['T']))]+=1
    for k in sorted(c): print('   %-28s %d' % (k, c[k]))
