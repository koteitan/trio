"""after_w の枝を機械生成の 5 選言に置き換える写し rows3l.py。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", '''LX = {'aw5': False}


def _par(m, x, k):
    for q in range(x - 1, -1, -1):
        if m[q][k] < m[x][k]:
            return q
    return -1


def aw_deep(Mo, off):
    """`after_w` の枝で深く綴るか（課題 H6、機械生成の 5 選言）。"""
    n = len(Mo); p = tuple(Mo[off])
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else (-9, -9, -9)
    br = lambda c: c[1] == 1 and c[2] == 0 and c[0] >= 2
    nx2 = g(off + 2); pv2 = g(off - 2); pv3 = g(off - 3)
    ch = [t for t in range(n) if copy_head(Mo, t)]
    blk_ge5 = len(ch) >= 2 and (ch[1] - ch[0]) >= 5
    a01 = _par(Mo, off, 0)
    a02 = _par(Mo, a01, 0) if a01 >= 0 else -1
    a03 = _par(Mo, a02, 0) if a02 >= 0 else -1
    a03_chead = a03 >= 0 and copy_head(Mo, a03)
    a01_far = a01 >= 0 and off - a01 > 3
    a01_r1_eq = a01 >= 0 and Mo[a01][1] == p[1]
    a01_r2_eq = a01 >= 0 and Mo[a01][2] == p[2]
    a02_r1_d1 = a02 >= 0 and Mo[a02][1] == p[1] - 1
    hi = hi_block2(Mo, off) if V14['h1'] else hi_block(Mo, off)
    return ((not blk_ge5 and nx2[2] > 0)
            or ((not a03_chead) and hi)
            or (pv2[2] != p[2])
            or (a01_far and (not br(pv3)) and pv3[1] == p[1])
            or (a01_r1_eq and (not a01_r2_eq) and (not a02_r1_d1)))


V12 = {''', 1)
old = """            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)"""
new = """            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)
                if LX['aw5']:
                    shallow = not aw_deep(Mo, off)"""
assert src.count(old)==1
src = src.replace(old,new,1)
open('/tmp/h1work/rows3l.py','w').write(src)
print('ok')
