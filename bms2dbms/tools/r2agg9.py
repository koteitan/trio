"""9 列の 4 分割の結果をまとめる。"""
import pickle, sys
from collections import Counter
D = '/home/koteitan/proofs/dbms/bms2dbms/tools/'
C = Counter(); n = 0; F = []
for i in range(4):
    d = pickle.load(open(D + 'r2_9_%d.pkl' % i, 'rb'))
    C.update(d['c']); n += d['n']; F += d['forest']
print('== 9 列 全数  母数 %d' % n)
for k in sorted(C):
    print('   %-20s %d' % (k, C[k]))
print('木の本数の分布（記録した %d 件）: %s'
      % (len(F), sorted(Counter(len(f['trees']) for f in F).items())))
print('森の `d` の分布:', sorted(Counter(f['d'] for f in F).items()))
tt = [t for f in F for t in f['trees']]
print('木 %d 本のうち omin == rd:' % len(tt),
      sum(1 for t in tt if t['omin'] == t['rd']))
print('余裕 min_k rd_k - d の分布:',
      sorted(Counter(min(t['rd'] for t in f['trees']) - f['d'] for f in F).items()))
for k in (1, 2, 3, 4, 5):
    print('  陽性対照 T3(min rd >= d+%d) の破れ %d/%d' % (
        k, sum(1 for f in F if min(t['rd'] for t in f['trees']) < f['d'] + k),
        len(F)))
big = [f for f in F if len(f['trees']) >= 3]
print('木が 3 本以上（記録内）:', len(big))
for f in big[:5]:
    print('   ', ''.join(str(c).replace(' ', '') for c in f['M']),
          'd=', f['d'], [(t['m0'], t['rd'], t['omin']) for t in f['trees']])
