# -*- coding: utf-8 -*-
"""本番用パッチ: prev == 0 の枝を term_top(Mo, off+1) 1 つにする（課題 H6）。"""
import sys
SRC='/home/koteitan/proofs/dbms/tools/dbms/rows3.py'
src=open(SRC).read()

old = "def wchain_head(Mo, off):"
new = '''def p0_shallow(Mo, off):
    """`prev == 0` の枝: 分岐列を浅く綴るか。課題 H6。

        浅い  <=>  `off` が最後の柱  or  `term_top(Mo, off + 1)`

    つまり**次の柱が「行 1 の加算項の頭」なら浅い**。`term_top` は課題 H1 で
    作った述語（根 / アンカー (1,1,0) / 根の写し (k,0,0) / アンカーの写し (k,1,0)）
    なので、これは `closes_unit` を写しの中まで届くように読み替えたものになる。

    教師データ（シート 1354 行 ＋ ImgClosedT の目標）で測ると:

        `prev == 0` の枝 6480 本 …… **食い違い 0**（浅い 4017 / 深い 2463）
        ホールドアウト検定（行列で半分に割って当てはめ）…… 正例 1257/1257、
        負例 1972 本に**誤発火 0**
        `closes` の枝 6895 本でも**食い違い 0**

    これ 1 本で `closes_top` / `closes_unit` / `p0deep_ok` の 3 段重ねを置き換え、
    `p0deep_ok` が外していた 24 本も 0 本になる。
    （`prev != 0` の枝には当てられない。`plain` 31126 本では 3192 本外す。）
    """
    return off + 1 >= len(Mo) or term_top(Mo, off + 1)


def wchain_head(Mo, off):'''
assert src.count(old)==1
src=src.replace(old,new,1)

old = """                if cw:
                    shallow = True
                elif st['prev'] == 0 and not closes_unit(nxt):
                    _w0 = p0deep_ok(Mo, off, p, nxt)
                    shallow = not _w0"""
new = """                if st['prev'] == 0:
                    # 課題 H6: `prev == 0` の枝は `p0_shallow` 1 つで完全に決まる
                    # （教師データ 6480 本で食い違い 0）。`closes_top` /
                    # `closes_unit` / `p0deep_ok` の 3 段重ねを置き換える。
                    _w0 = not p0_shallow(Mo, off)
                    shallow = not _w0
                elif cw:
                    shallow = True"""
assert src.count(old)==1
src=src.replace(old,new,1)

if len(sys.argv)>1 and sys.argv[1]=='apply':
    open(SRC,'w').write(src); print('rows3.py を書き換えた')
else:
    src=src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                    "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
    open('/tmp/h1work/rows3P_tt.py','w').write(src); print('/tmp/h1work/rows3P_tt.py を書いた')
