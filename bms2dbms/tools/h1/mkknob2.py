# -*- coding: utf-8 -*-
"""H17: rows3k2 に FIRE / SITES（site ごとの入れ切り）を足す。"""
src = open('/tmp/h1work/rows3k2.py').read()
src = src.replace("KN = dict.fromkeys(", "FIRE = []\nSITES = [None]\n\n\nKN = dict.fromkeys(", 1)
a = """    dB = d
    if (KN['sb'] and lad1 and B and dd > d
            and (not KN['sb_w'] or (B[0][1] == 0 and B[0][2] == 0))):
        dB = dd"""
b = """    dB = d
    if (KN['sb'] and lad1 and B and dd > d
            and (not KN['sb_w'] or (B[0][1] == 0 and B[0][2] == 0))
            and (SITES[0] is None or off in SITES[0])):
        FIRE.append((off, tuple(p), tuple(B[0])))
        dB = dd"""
assert src.count(a) == 1
src = src.replace(a, b, 1)
src += '''

def b2d3k(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3k2.py', 'w').write(src)
print('ok')
