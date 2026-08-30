# -*- coding: utf-8 -*-
"""H11: 破れの現場を 1 件ずつ詳しく見る。"""
import sys, pickle
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
from core import show
rows = pickle.load(open('/tmp/h1work/h11rows.pkl', 'rb'))
ok = [r for r in rows if r['tag'] == 'ok']
lim = int(sys.argv[1]) if len(sys.argv) > 1 else 8
sel = sys.argv[2] if len(sys.argv) > 2 else None
n = 0
for r in ok:
    if sel and sel not in str(r['why']):
        continue
    n += 1
    if n > lim:
        break
    R, R0 = r['R'], r.get('R0')
    print('=== A=%s  m=%d  n=%d  bp=%s cpy=%s'
          % (show([list(x) for x in r['A']]), r['m'], r['n'],
             r.get('bp'), r.get('cpy')))
    print('  E=%s' % show([list(x) for x in r['E']]))
    print('  T=%s' % show([list(x) for x in r['T']]))
    print('  C=%s' % show([list(x) for x in r['C']]))
    print('  k=%d  want=%s got=%s   off=%d 柱=%s  why=%s ctx=%s isbr=%s'
          % (r['k'], r['want'], r['got'], r['off'], r['col'], r['why'],
             r['ctx'], r['isbr']))
    if R:
        print('  この柱   first=%s ps=%s d=%s nA=%s force=%s F=%s'
              % (R['first'], R['ps'], R['d'], R['nA'], R['force'], R['F']))
        print('           L=%s' % (R['L'],))
    if R0:
        print('  写し a-1 first=%s ps=%s d=%s nA=%s force=%s 柱=%s'
              % (R0['first'], R0['ps'], R0['d'], R0['nA'], R0['force'],
                 r.get('col0')))
        print('           L=%s' % (R0['L'],))
    print()
