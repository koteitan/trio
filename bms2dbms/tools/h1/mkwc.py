# -*- coding: utf-8 -*-
"""H17: `wchain` の決定を反転する旗 rows3w2.py（WCFLAGS=wcinv,wcgate）。

α に移った 2 個（`conv3(A)` 自身の綴り）はどちらも `wchain/deep` で、
`awflip` は `after_w` の枝にしか掛かっていない。
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
HEAD = ("WC = {'wcinv': False, 'wcgate': False, 'wcaw': False}\n"
        "for _k in os.environ.get('WCFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in WC, _k\n"
        "        WC[_k.strip()] = True\n"
        "FIRE = []\nSITES = [None]\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
GATE = '\n'.join([
 "def wc_gate(Mo, off):",
 "    return True",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
old = """                if j is not None:
                    shallow = not (hi and not (_p0(Mo, j) == 0))"""
new = """                if j is not None:
                    shallow = not (hi and not (_p0(Mo, j) == 0))
                    if ((WC['wcinv']
                         or (WC['wcaw'] and aw_flip(Mo, off))
                         or (WC['wcgate'] and wc_gate(Mo, off)))
                            and (SITES[0] is None or off in SITES[0])):
                        FIRE.append((off, tuple(p), shallow))
                        shallow = not shallow"""
assert src.count(old) == 1
src = src.replace(old, new, 1)
src += '''

def b2d3wc(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3w2.py', 'w').write(src)
print('ok')
