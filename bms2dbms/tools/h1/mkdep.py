# -*- coding: utf-8 -*-
"""H16: 縮約が兄弟 `cB` と残余 `cR` に渡す**深さ**を 1 段深くする旗（rows3e2.py）。

族 δ の 6 個はどれも「縮約の中で深さが 1 だけ浅い」だった:
    cB … 兄弟ブロックまるごと 1 段浅い（want (2,0,0) got (1,0,0)）
    cR … 残余の末尾が 1 段浅い（want (5,1,0) got (4,1,0)）
DPFLAGS=cbd1,crd1,cbgate,crgate
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
HEAD = ("DP = {'cbd1': False, 'crd1': False, 'cbgate': False, 'crgate': False}\n"
        "for _k in os.environ.get('DPFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in DP, _k\n"
        "        DP[_k.strip()] = True\n"
        "FIRE = []\nSITES = [None]\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
GATE = '\n'.join([
 "def cb_gate(Mo, off):",
 "    return True",
 "",
 "",
 "def cr_gate(Mo, off):",
 "    return True",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
old = """            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
new = """            _dB = d
            if (DP['cbd1'] and Bq and (SITES[0] is None or oBq in SITES[0])
                    and (not DP['cbgate'] or cb_gate(st['Mo'], oBq))):
                _dB = d + 1
                FIRE.append((oBq, tuple(Bq[0]), 'cB'))
            cB = conv3(Bq, _dB, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
assert src.count(old) == 1
src = src.replace(old, new, 1)
old2 = "            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)"
new2 = """            _rd = rd
            if (DP['crd1'] and rest2 and (SITES[0] is None or oR in SITES[0])
                    and (not DP['crgate'] or cr_gate(st['Mo'], oR))):
                _rd = rd + 1
                FIRE.append((oR, tuple(rest2[0]), 'cR'))
            cR = conv_resid(rest2, _rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)"""
assert src.count(old2) == 1
src = src.replace(old2, new2, 1)
src += '''

def b2d3e(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3e2.py', 'w').write(src)
print('ok')
