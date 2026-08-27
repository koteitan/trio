"""after_w の枝を 2 選言に置き換える写し rows3p.py（課題 H8）。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", '''NX = {'aw2': False}


def aw_deep2(Mo, off):
    """`after_w` の枝で深く綴るか（課題 H8、2 選言）。

        深い <=> (写しのブロックが 5 列未満 かつ 2 つ先の柱が行 2 を使う)
                 or (3 つ前の柱の行 1 が自分と同じ かつ
                     いまの項の中の「行 2 を使う柱」がちょうど 1 本ではない)
    """
    n = len(Mo); p = tuple(Mo[off])
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else (-9, -9, -9)
    ch = [t for t in range(n) if copy_head(Mo, t)]
    blk_ge5 = len(ch) >= 2 and (ch[1] - ch[0]) >= 5
    nx2_z = g(off + 2)[2] > 0
    pv3_r1_eq = g(off - 3)[1] == p[1]
    th = 0
    for t in range(off - 1, -1, -1):
        if term_top(Mo, t):
            th = t; break
    zblk1 = sum(1 for t in range(th, off) if Mo[t][2] > 0) == 1
    return ((not blk_ge5 and nx2_z) or (pv3_r1_eq and not zblk1))


V12 = {''', 1)
old = """            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)"""
new = """            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)
                if NX['aw2']:
                    shallow = not aw_deep2(Mo, off)"""
assert src.count(old)==1
src = src.replace(old,new,1)
open('/tmp/h1work/rows3p.py','w').write(src)
print('ok')
