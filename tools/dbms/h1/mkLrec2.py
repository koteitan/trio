# -*- coding: utf-8 -*-
"""H11: conv3 の各呼び出しで (off, first, force, ps, pw, d, L, F, nA, nM, ctx)
を記録する写し rows3F.py。mkLrec.py の拡張（split0 の切れ目 nA と、
縮約の中のどの再帰か ctx を足した）。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", "LREC = []\nCTX = []\n\n\nV12 = {", 1)
old = "    oA, oB = off + 1, off + 1 + len(A)      # 引数ブロック / 兄弟の先頭の添字\n"
new = (old +
       "    LREC.append(dict(off=off, L=tuple(tuple(x) for x in L), F=tuple(F),\n"
       "                     d=d, ps=tuple(ps), pw=tuple(pw), first=first,\n"
       "                     force=force, p=tuple(p), nM=len(M), nA=len(A),\n"
       "                     ctx=tuple(CTX)))\n")
assert src.count(old) == 1
src = src.replace(old, new, 1)

CTXR = [
    ("            cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,\n"
     "                       U[0] if U else na, oA)\n", 'cA'),
    ("            cU = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,\n"
     "                       oU)\n", 'cU'),
    ("            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)\n", 'cR'),
    ("            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,\n"
     "                       oBq)\n", 'cB'),
]
for a, tag in CTXR:
    assert src.count(a) == 1, ('見つからない', tag)
    src = src.replace(a, "            CTX.append('%s')\n" % tag + a + "            CTX.pop()\n", 1)

src += '''

def b2d3F(M):
    """(像, LREC) の対。LREC は conv3 の呼び出しごとに 1 件。"""
    del LREC[:]
    del CTX[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    return out, list(LREC)
'''
open('/tmp/h1work/rows3F.py', 'w').write(src)
print('ok')
