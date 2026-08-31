# -*- coding: utf-8 -*-
"""H8: 一致する対（conv3(A<n>) == (conv3 A)<m>）から `after_w` の負例を大量に作る。
   正例は今までどおり「ずれ -1 の教師データで深いのに浅いと言っている」site。"""
import sys, pickle, time
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, provh, core
from rows3 import is_branch
from core import expand

WHICH = sys.argv[1] if len(sys.argv) > 1 else 'aw'
LIM = int(sys.argv[2]) if len(sys.argv) > 2 else 6
NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 4

def sel(why):
    return why.startswith('after_w') if WHICH == 'aw' else why.startswith('plain')

# --- 1) 一致する対から「いまの決定が正しい」site を集める（負例の山）------
A = sorted(rows3.gen3('BMS', LIM, zcap=1), key=rows3.key)
neg = {}
t0 = time.time()
for i, M in enumerate(A):
    if len(M) < 2: continue
    if i % 2000 == 0:
        core._exp_memo.clear(); core._isstd_memo.clear(); core._flat_memo.clear()
    Mt = tuple(map(tuple, M)); fM = tuple(map(tuple, rows3.b2d3(list(M))))
    Ls = {}
    for m in range(1, 7):
        T = tuple(expand(fM, m)); Ls.setdefault(len(T), []).append(T)
    for n in range(1, NMAX + 1):
        E = tuple(tuple(x) for x in expand(Mt, n))
        U, pr = provh.b2d3p(list(E))
        if not any(U == T for T in Ls.get(len(U), ())):
            continue                       # ぴったり一致する対だけ使う
        for q, pe in zip(U, pr):
            k, off, why, d = pe[0], pe[1], pe[2], pe[4]
            if k != 'body' or d is None or d.get('why') == 'tie': continue
            if not is_branch(E[off]) or not sel(d['why']): continue
            neg[(E, off)] = d['shallow']    # いまの決定が正しい
print('一致する対から取れた %s の site %d 個  %.0fs' % (WHICH, len(neg), time.time()-t0))

# --- 2) 正例（教師データで直すべき site）---------------------------------
tab, cur, dec, want = pickle.load(open('/tmp/h1work/h6tab.pkl','rb'))
pos = {}
for k in tab:
    d = dec[k]
    if d.get('shallow') is None or not sel(d['why']): continue
    if cur[k] != tab[k]: pos[k] = tab[k]
    else: neg.setdefault(k, tab[k])
print('教師データの正例（直すべき）%d 個 / 負例あわせて %d 個' % (len(pos), len(neg)))
for k in pos: neg.pop(k, None)
pickle.dump((pos, neg), open('/tmp/h1work/h8big_%s.pkl' % WHICH, 'wb'))
