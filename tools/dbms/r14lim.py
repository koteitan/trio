# -*- coding: utf-8 -*-
"""現在の rows3.py を基準に、tiesd の入れ方を 3 通り比べる。"""
import sys, os
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3
MODE = sys.argv[1]; lim = int(sys.argv[2])
_t = rows3.tie_sd
if MODE == 'guard':          # tiesd を on にして「行列の末尾では発火しない」門
    rows3.V18['tiesd'] = True
    rows3.tie_sd = lambda Mo, off: False if off == len(Mo) - 1 else _t(Mo, off)
elif MODE == 'on':           # tiesd を素で on
    rows3.V18['tiesd'] = True
print('== tiesd の入れ方 =', MODE, '（既定は off）')
rows3.main(lim=lim, imgc=3)
