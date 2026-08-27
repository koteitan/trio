# -*- coding: utf-8 -*-
"""縮約の cB の付け場所（d か d+1 か）の教師つきデータ。
   正解は onto.py の目標 T（DBMS 標準形）そのもの。"""
import sys, pickle, itertools, time
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3e
from inv3 import d2b3
from core import isstd, show

def sites_of(B):
    rows3e.CBREC[0]=True; del rows3e.CBSITES[:]; rows3e.CBFORCE.clear()
    rows3e.b2d3(list(B)); rows3e.CBREC[0]=False
    out, seen = [], set()
    for s in rows3e.CBSITES:
        if s['off'] in seen: continue
        seen.add(s['off']); out.append(s)
    return out

def run(B, force):
    rows3e.CBFORCE.clear(); rows3e.CBFORCE.update(force)
    try: q = tuple(rows3e.b2d3(list(B)))
    except Exception: q = None
    rows3e.CBFORCE.clear()
    return q

def collect(lim=7, zcap=1, verbose=1):
    D = sorted(rows3.gen3('DBMS', lim, zcap=zcap), key=rows3.key)
    pos, neg, c = [], [], Counter()
    for T in D:
        T = tuple(map(tuple, T))
        try: B = d2b3(T)
        except Exception: B = None
        if not B or not isstd(B,'BMS') or any(x[2] > 1 for x in B):
            c['B なし/非標準'] += 1; continue
        Bt = tuple(map(tuple, B))
        S = sites_of(list(B))
        base = run(list(B), ())
        if base == T:
            c['もともと全射'] += 1
            for s in S:                          # 1 site ずつ強制して壊れるか
                if run(list(B), (s['off'],)) != T:
                    neg.append(dict(B=Bt, T=T, off=s['off'], site=s)); c['負例'] += 1
                else:
                    c['強制しても変わらない'] += 1
            continue
        c['いま外れ'] += 1
        hit = None
        for r in range(1, min(len(S),3)+1):
            for cc in itertools.combinations([s['off'] for s in S], r):
                if run(list(B), cc) == T: hit = cc; break
            if hit: break
        if hit is None:
            c['cB では直らない'] += 1
            continue
        c['cB で直る（force %d 本）' % len(hit)] += 1
        sm = {s['off']: s for s in S}
        for o in hit:
            pos.append(dict(B=Bt, T=T, off=o, site=sm[o]))
    if verbose:
        for k in sorted(c): print('   %-24s %d' % (k, c[k]))
        print('   正例 %d / 負例 %d' % (len(pos), len(neg)))
    return pos, neg

if __name__ == '__main__':
    lim = int(sys.argv[1]) if len(sys.argv)>1 else 7
    t0=time.time()
    P, N = collect(lim)
    pickle.dump((P,N), open('/tmp/h1work/cb_data%d.pkl'%lim,'wb'))
    print('%.0fs' % (time.time()-t0))
