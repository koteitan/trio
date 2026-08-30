# -*- coding: utf-8 -*-
"""H13: ImgCofinalT で本当に破れている A だけを取り出して pickle に。"""
import sys, pickle
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import cofinal, rows3
from core import show
lim = int(sys.argv[1]) if len(sys.argv) > 1 else 6
nbad, still = cofinal.score(lim, 16, verbose=0)
print('lim=%d: ImgClosedT の破れ %d -> **ImgCofinalT の破れ %d**' % (lim, nbad, len(still)))
pickle.dump([A for A, p in still], open('/tmp/h1work/cof%d.pkl' % lim, 'wb'))
for A, p in still:
    print('   %-52s %s' % (show(list(A)), p))
