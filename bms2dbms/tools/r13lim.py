# -*- coding: utf-8 -*-
"""門つき（`tie_sd` / `aw_flip` を行列の末尾で発火させない）で lim の 7 土俵を回す。"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3
MODE = sys.argv[1]; lim = int(sys.argv[2])
_tie, _aw = rows3.tie_sd, rows3.aw_flip
if MODE in ('tie', 'both'):
    rows3.tie_sd = lambda Mo, off: False if off == len(Mo) - 1 else _tie(Mo, off)
if MODE in ('aw', 'both'):
    rows3.aw_flip = lambda Mo, off: False if off == len(Mo) - 1 else _aw(Mo, off)
print('門 =', MODE)
rows3.main(lim=lim, imgc=3)
