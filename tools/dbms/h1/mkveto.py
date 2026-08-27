"""closes_top の拒否権（H6 で機械生成の素性から出した 4 選言）を旗で入れる写し rows3k.py。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", '''KX = {'veto': False, 'veto1': False, 'veto12': False, 'veto123': False}


def _par(m, x, k):
    for q in range(x - 1, -1, -1):
        if m[q][k] < m[x][k]:
            return q
    return -1


def ct_veto(Mo, off):
    """`closes_top` を止めるか（課題 H6、機械生成の素性から）。"""
    n = len(Mo); p = tuple(Mo[off])
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else (-9, -9, -9)
    br = lambda c: c[1] == 1 and c[2] == 0 and c[0] >= 2
    nx3 = g(off + 3); pv1 = g(off - 1); pv2 = g(off - 2)
    a11 = _par(Mo, off, 1); a01 = _par(Mo, off, 0)
    a11_adj = a11 >= 0 and off - a11 == 1
    a01_r1_d1 = a01 >= 0 and Mo[a01][1] == p[1] - 1
    anch = any(tuple(c) == ANCHOR for c in Mo[:off])
    wch = wchain_head(Mo, off) is not None
    d1 = br(nx3) and wch
    d2 = a11_adj and br(nx3) and not (pv2[2] == p[2])
    d3 = a01_r1_d1 and br(pv1)
    d4 = (a11_adj and not anch and not br(nx3) and nx3[1] == p[1] and br(pv2))
    if KX['veto1']:
        return d1
    if KX['veto12']:
        return d1 or d2
    if KX['veto123']:
        return d1 or d2 or d3
    return d1 or d2 or d3 or d4


V12 = {''', 1)
old = """                if cw:
                    shallow = True"""
new = """                if cw and (not (KX['veto'] or KX['veto1'] or KX['veto12']
                                or KX['veto123'])
                           or not ct_veto(Mo, off)):
                    shallow = True
                elif cw:
                    pass"""
assert src.count(old)==1
src = src.replace(old,new,1)
open('/tmp/h1work/rows3k.py','w').write(src)
print('ok')
