# -*- coding: utf-8 -*-
"""課題 H6 (1): 目標の行 1 は base_s / base_d / base_sd のどれか。
   どれとも違うものがあれば、2 択という設計そのものが足りない。"""
import sys, pickle
from collections import Counter
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/bms2dbms/tools')
from h1an import load
from core import show

R = load('S.pkl','T6_6.pkl','T7_4.pkl')
tab, cur, dec, want = {}, {}, {}, {}
confl = 0
for r in R:
    k = (r['A'], r['off'])
    if k in tab and tab[k] != r['shallow']:
        confl += 1; continue
    tab[k] = r['shallow']; cur[k] = r['dec']['shallow']; dec[k] = r['dec']
    if 'want' in r: want[k] = r['want']
print('サイト %d  矛盾 %d' % (len(tab), confl))
print('(いまの決定, 正解):', dict(Counter((cur[k], tab[k]) for k in tab)))
err = [k for k in tab if cur[k] != tab[k]]
print('誤り %d  内訳:' % len(err), dict(Counter(dec[k]['why'] for k in err)))
print()
print('=== 誤り %d 本について 目標の行 1 が何に一致するか ===' % len(err))
c = Counter(); other = []
for k in err:
    d = dec[k]
    w = want.get(k)
    if w is None:
        c['want 不明（シート由来）'] += 1; continue
    wv = w[1]
    tags = []
    if wv == d['base_s']: tags.append('base_s')
    if wv == d['base_d']: tags.append('base_d')
    if wv == d['base_sd']: tags.append('base_sd')
    if wv == d['deep']: tags.append('deep(=採用した深い側)')
    lab = '+'.join(tags) if tags else '**どれとも違う**'
    c[(dec[k]['why'], lab)] += 1
    if not tags:
        other.append((k, d, w))
for kk in sorted(c, key=str): print('   %-40s %d' % (str(kk), c[kk]))
print()
print('どれとも違う: %d 本' % len(other))
for (A,off), d, w in other[:40]:
    print('   %-62s off=%-3d p=%s' % (show([list(x) for x in A])[:62], off, A[off]))
    print('      want[1]=%s  base_s=%s base_d=%s base_sd=%s deep=%s  why=%s'
          % (w[1], d['base_s'], d['base_d'], d['base_sd'], d['deep'], d['why']))
pickle.dump((tab,cur,dec,want), open('/tmp/h1work/h6tab.pkl','wb'))
