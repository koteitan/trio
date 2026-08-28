# -*- coding: utf-8 -*-
"""H16: `cB の d+1` と `sbody`（影の兄弟を本体の横に）を**同時に**入れる写し rows3f2.py。
族 δ は 2 か所同時の変更が要る、という仮説の検証用。DP2FLAGS=cbd1,sb,sb_w
"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = ("D2 = {'cbd1': False, 'sb': False, 'sb_w': False, 'crd1': False}\n"
        "for _k in os.environ.get('DP2FLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in D2, _k\n"
        "        D2[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
a = """            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
b = """            cB = conv3(Bq, d + (1 if (D2['cbd1'] and Bq) else 0), L, FA,
                       (v, s2), (e1, e2), False, False, st, nx, oBq)"""
assert src.count(a) == 1
src = src.replace(a, b, 1)
c = "            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)"
d = ("            cR = conv_resid(rest2, rd + (1 if (D2['crd1'] and rest2) else 0),\n"
     "                            Lr, (v, s2), (e1, e2), st, hd(Bq), oR)")
assert src.count(c) == 1
src = src.replace(c, d, 1)
e = "    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)"
f = ("    dB = d\n"
     "    if (D2['sb'] and lad1 and B and dd > d\n"
     "            and (not D2['sb_w'] or (B[0][1] == 0 and B[0][2] == 0))):\n"
     "        dB = dd\n"
     "    cB = conv3(B, dB, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)")
assert src.count(e) == 1
src = src.replace(e, f, 1)
open('/tmp/h1work/rows3f2.py', 'w').write(src)
print('ok')
