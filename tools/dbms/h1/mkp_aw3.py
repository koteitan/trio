# -*- coding: utf-8 -*-
"""本番用パッチ: after_w の枝を 2 選言＋拒否権にする（課題 H8）。"""
import sys
SRC='/home/koteitan/proofs/dbms/tools/dbms/rows3.py'
src=open(SRC).read()

old = "def wchain_head(Mo, off):"
new = '''def par_row(m, x, k):
    """行 `k` の親（左にある、行 k の値がより小さい直近の柱）。無ければ -1。"""
    for q in range(x - 1, -1, -1):
        if m[q][k] < m[x][k]:
            return q
    return -1


def term_head_before(Mo, off):
    """`off` より前の直近の「行 1 の加算項の頭」の添字（無ければ 0）。"""
    for t in range(off - 1, -1, -1):
        if term_top(Mo, t):
            return t
    return 0


def aw_deep(Mo, off):
    """`after_w` の枝で分岐列を深く綴るか。課題 H8。

        深い <=> (写しのブロックが 5 列未満 かつ 2 つ先の柱が行 2 を使う)
                 or (3 つ前の柱の行 1 が自分と同じ かつ
                     いまの項の中の「行 2 を使う柱」がちょうど 1 本ではない)
                 ただし
                 (行 0 の祖先 2 段目の行 1 が p[1]-1 かつ 2 つ先の柱の行 0 が p[0]-1)
                 のときは浅い

    **行 2 は展開で変わらない**ので、行 2 だけを見た量は写しに完全に同変である。
    いまの項（`term_top` から）の中の行 2 の柱を数える `zblk` がこの枝の要になる。

    教師データ（`after_w` の枝 264 site、正解が深い 123 / 浅い 141）で
    **123/123 を fp=0 で覆う**。ホールドアウト検定（3 通りの分割）で
    正例 63/63・62/62・63/63、負例への誤発火 1・0・1。
    「ずらしを全部見る一致」（lim=6 で 50762 組）を **1 組も壊さない**。
    """
    n = len(Mo); p = tuple(Mo[off])
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else (-9, -9, -9)
    ch = [t for t in range(n) if copy_head(Mo, t)]
    blk_ge5 = len(ch) >= 2 and (ch[1] - ch[0]) >= 5
    th = term_head_before(Mo, off)
    zblk1 = sum(1 for t in range(th, off) if Mo[t][2] > 0) == 1
    deep = ((not blk_ge5 and g(off + 2)[2] > 0)
            or (g(off - 3)[1] == p[1] and not zblk1))
    if deep:
        a01 = par_row(Mo, off, 0)
        a02 = par_row(Mo, a01, 0) if a01 >= 0 else -1
        if (a02 >= 0 and Mo[a02][1] == p[1] - 1
                and g(off + 2)[0] == p[0] - 1):
            deep = False
    return deep


def wchain_head(Mo, off):'''
assert src.count(old)==1
src=src.replace(old,new,1)

old = """            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)"""
new = """            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                # 課題 H8: `after_w` の枝は `aw_deep` 1 本で決まる。
                # もとの `not (hi and not (par0(Mo, off-1) == 0))` は
                # `st['prev']` / 直前 1 本 / 根の判定 という写しに同変でない
                # 読みを 3 つ使っていた。
                shallow = not aw_deep(Mo, off)"""
assert src.count(old)==1
src=src.replace(old,new,1)

if len(sys.argv)>1 and sys.argv[1]=='apply':
    open(SRC,'w').write(src); print('rows3.py を書き換えた')
else:
    src=src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                    "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
    open('/tmp/h1work/rows3P_aw3.py','w').write(src); print('/tmp/h1work/rows3P_aw3.py を書いた')
