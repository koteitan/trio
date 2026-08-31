# -*- coding: utf-8 -*-
"""H14 (4): 影の兄弟を本体の横 `dd` に付ける条項 `sbody` を旗で（rows3b.py）。

課題 H12 で `sbody_w`（兄弟の頭が「x w」のときだけ）は +0 / -17075 で却下したが、
そのときは教師データが**正例 1 本**しかなかった。H13 の教訓（遠くを見る素性）を
使ってやり直す。SBFLAGS2=sb,sb_w,sb_gate
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
HEAD = ("BF = {'sb': False, 'sb_w': False, 'sb_gate': False}\n"
        "for _k in os.environ.get('SBFLAGS2', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in BF, _k\n"
        "        BF[_k.strip()] = True\n"
        "FIRE = []\nSITES = [None]\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
GATE = '\n'.join([
 "def sb_gate(Mo, off):",
 "    # H14: a01_chead — 行 0 の親が**写しの頭**（正例 10/10 / 負例 10, fp=0）",
 "    q = par0(Mo, off)",
 "    return q >= 0 and copy_head(Mo, q)",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
old = "    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)"
new = ("    dB = d\n"
       "    if (BF['sb'] and lad1 and B and dd > d\n"
       "            and (not BF['sb_w'] or (B[0][1] == 0 and B[0][2] == 0))\n"
       "            and (SITES[0] is None or off in SITES[0])\n"
       "            and (not BF['sb_gate'] or sb_gate(st['Mo'], off))):\n"
       "        FIRE.append((off, tuple(p), d, dd, tuple(B[0])))\n"
       "        dB = dd\n"
       "    cB = conv3(B, dB, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)")
assert src.count(old) == 1
src = src.replace(old, new, 1)
src += '''

def b2d3b(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3b.py', 'w').write(src)
print('ok')
