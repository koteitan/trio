"""conv3 の各呼び出しで (off, L, F, d, ps, pw) を記録する写し rows3L.py（課題 H10）。"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {", "LREC = []\n\n\nV12 = {", 1)
old = "    p, r = M[0], M[1:]\n"
new = ("    p, r = M[0], M[1:]\n"
       "    LREC.append(dict(off=off, L=tuple(tuple(x) for x in L), F=tuple(F),\n"
       "                     d=d, ps=tuple(ps), pw=tuple(pw), first=first,\n"
       "                     force=force, p=tuple(p), n=len(M)))\n")
assert src.count(old)==1
src = src.replace(old,new,1)
src += '''

def b2d3L(M):
    """(像, LREC) の対。LREC は conv3 の呼び出しごとに 1 件。"""
    del LREC[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    return out, list(LREC)
'''
open('/tmp/h1work/rows3L.py','w').write(src)
print('ok')
