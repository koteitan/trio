# -*- coding: utf-8 -*-
"""H11: 条項 `sibnb` の発火場所に正例/負例のラベルを付ける。

負例（発火してはいけない）: シートの BMS 行で、素の conv3 は正解なのに
                            その 1 か所だけ発火させると像が変わる場所。
正例（発火すべき）:         ImgClosedT の破れ (A,m,T) で、E=A<n> の
                            その 1 か所を発火させると T にぴったり当たる場所。
"""
import sys, os, pickle
os.environ['SBFLAGS'] = 'sibnb'
sys.path.insert(0, '/tmp/h1work')
sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')
import rows3, rows3s, sheet3
from core import expand, show

NEG, POS = [], []

# ---- 負例: シート
T = sheet3.load(1)
nch = 0
for row, b, d in T:
    E = tuple(map(tuple, b))
    o0 = tuple(map(tuple, rows3.b2d3(list(E))))
    if o0 != tuple(map(tuple, d)):
        continue                       # 素で外している行（4 行）は使わない
    _, F = rows3s.b2d3f(list(E), sites=set())
    if not F:
        _, F = rows3s.b2d3f(list(E))   # 発火場所を知るために一度全開で
    offs = sorted(set(f[0] for f in F))
    if not offs:
        continue
    for off in offs:
        o1, _ = rows3s.b2d3f(list(E), sites={off})
        if o1 != o0:
            NEG.append((E, off))
            nch += 1
print('負例: シート %d 行 / 発火して像が変わる場所 %d' % (len(T), nch))

# ---- 正例: ImgClosedT の破れ
bad = pickle.load(open('/tmp/h1work/img54p.pkl', 'rb'))
npos = 0
for A, m, Tg in bad:
    S = tuple(map(tuple, A))
    Tg = tuple(map(tuple, Tg))
    for n in range(1, 10):
        E = [tuple(x) for x in expand(S, n)]
        if not E:
            break
        o0 = tuple(map(tuple, rows3.b2d3(list(E))))
        if len(o0) > len(Tg) + 6:
            break
        oall, F = rows3s.b2d3f(list(E))
        if oall != Tg:
            continue
        offs = sorted(set(f[0] for f in F))
        # 1 か所ずつ発火させて当たるものを正例に
        hit = [off for off in offs
               if rows3s.b2d3f(list(E), sites={off})[0] == Tg]
        use = hit if hit else offs
        for off in use:
            POS.append((tuple(E), off))
            npos += 1
        break
print('正例: 破れ %d 対 / 発火すべき場所 %d' % (len(bad), npos))
pickle.dump((POS, NEG), open('/tmp/h1work/h11sites.pkl', 'wb'))
# 重なりを見る
sp, sn = set(POS), set(NEG)
print('相異なる 正例 %d / 負例 %d / 重なり %d' % (len(sp), len(sn), len(sp & sn)))
