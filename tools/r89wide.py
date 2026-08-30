# -*- coding: utf-8 -*-
"""**R89 その 5 —— 母集団を広げる（教訓 16）。**

グリッドを広げて、R89b の形の等式 (P1/P2/P3) と R89 の分布が動くかを見る。
とくに `c >= 2` / `z=1` / 深い行 0 を入れる。
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
from r89b import run as runb
from r89 import run as runa

DS = (1, 2, 3, 4); BS = (0, 1, 2, 3); CS = (0, 1, 2)
VS = (0, 1, 2, 3); ZS = (0, 1); TS = (0, 1, 2, 3)
CAPB = (0, 1, 2, 3, 4, 5); CAPC = (0, 1, 2, 3)
LS = (1, 2)

runb(DS, BS, CS, VS, ZS, TS, CAPB, CAPC, LS, 'WIDE 形の検算 |M|<=2 (48 列)')
runa(DS, BS, CS, VS, ZS, TS, CAPB, CAPC, LS, False, 9, 28,
     'WIDE 分布 |M|<=2 (CtxOK 無し)')
