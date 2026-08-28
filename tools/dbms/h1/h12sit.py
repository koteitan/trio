# -*- coding: utf-8 -*-
"""H12: 条項 `sbody`（影の兄弟を本体の横に付ける）の発火場所にラベルを付ける。

負例: シートの BMS 行で、素の conv3 は正解なのにその 1 か所だけ発火させると
      像が変わる場所。
正例: ImgClosedT の破れ (A,m,T) の**証人** B = d2b3(T) で、その 1 か所を
      発火させると conv3(B) == T になる場所（H2 の「証人は d2b3(T)」）。
"""
import sys, os, pickle
os.environ.setdefault('RFLAGS', 'sbody,sbody_w')
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')
import rows3, rows3r, sheet3, inv3
from core import expand, show, isstd

NEG, POS = [], []
T = sheet3.load(1)
for row, b, d in T:
    E = tuple(map(tuple, b))
    o0 = tuple(map(tuple, rows3.b2d3(list(E))))
    if o0 != tuple(map(tuple, d)):
        continue
    _, F = rows3r.b2d3f(list(E))
    for off in sorted(set(f[0] for f in F)):
        if rows3r.b2d3f(list(E), sites={off})[0] != o0:
            NEG.append((E, off))
print('負例（シート）: %d' % len(NEG))

bad = pickle.load(open('/tmp/h1work/img54p.pkl', 'rb'))
nw, nfix = 0, 0
for A, m, Tg in bad:
    Tg = tuple(map(tuple, Tg))
    B = inv3.d2b3([list(x) for x in Tg])
    if B is None:
        continue
    Bt = tuple(tuple(x) for x in B)
    if not isstd(Bt, 'BMS') or any(c[2] > 1 for c in Bt):
        continue
    nw += 1
    if tuple(map(tuple, rows3.b2d3(list(Bt)))) == Tg:
        continue                       # 素で当たっている（破れの原因は別）
    oall, F = rows3r.b2d3f(list(Bt))
    if oall != Tg:
        continue                       # この条項では直らない
    nfix += 1
    offs = sorted(set(f[0] for f in F))
    hit = [o for o in offs if rows3r.b2d3f(list(Bt), sites={o})[0] == Tg]
    for o in (hit if hit else offs):
        POS.append((Bt, o))
print('証人 B = d2b3(T) が取れた %d / この条項で直る %d / 正例 %d'
      % (nw, nfix, len(POS)))
sp, sn = set(POS), set(NEG)
print('相異なる 正例 %d / 負例 %d / 重なり %d' % (len(sp), len(sn), len(sp & sn)))
pickle.dump((sorted(sp - (sp & sn)), sorted(sn - (sp & sn))),
            open('/tmp/h1work/h12sites.pkl', 'wb'))
