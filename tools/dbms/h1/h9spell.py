# -*- coding: utf-8 -*-
"""H9 (1): `st['prev']` を行列と位置だけから導く `spell` を書き、いまの値と比べる。

    prev_of(Mo, off) : off より前の**同じ項の中の**直前の分岐列 j の綴り
                       （項の頭 `term_top` に当たったら None）
    spell(Mo, off)   : その prev を使って site の条項を当てた結果（浅いか）

`j < off` なので位置についての整礎な再帰。`conv3` の呼び出し順（縮約・残余・兄弟）
に依存しない。
"""
import sys
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
from rows3 import (is_branch, is_w_col, par0, hi_block, hi_block2, is_repeat,
                   closes_unit, closes_hi_unit, wchain_head, copy_head,
                   term_top, closes_top, p0_shallow, ANCHOR, V13, V14)

def _key(Mo):
    return tuple(map(tuple, Mo))

def prev_of(Mo, off, memo, skip_tie=None, nxts=None):
    """off より前の、同じ項の中の直前の分岐列の綴り。無ければ None。"""
    for j in range(off - 1, -1, -1):
        if term_top(Mo, j):
            return None
        if is_branch(Mo[j]):
            if skip_tie is not None and j in skip_tie:
                continue                    # tie の柱は prev を書き換えない
            return 0 if spell(Mo, j, memo, skip_tie, nxts) else 1
    return None

def spell(Mo, off, memo=None, skip_tie=None, nxts=None):
    """分岐列 Mo[off] を浅く綴るか。行列と位置だけで決まる。"""
    if memo is None: memo = {}
    k = (off,)
    if k in memo: return memo[k]
    n = len(Mo); p = tuple(Mo[off])
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else None
    nxt = (nxts.get(off, g(off + 1)) if nxts is not None else g(off + 1))
    pv = g(off - 1); pv2 = g(off - 2)
    prev = prev_of(Mo, off, memo, skip_tie, nxts)
    shallow = (prev == 0) or closes_unit(nxt)
    hi = hi_block2(Mo, off) if V14['h1'] else hi_block(Mo, off)
    if V14['h1']:
        cw = closes_top(Mo, off, nxt)
        if prev == 0:
            shallow = p0_shallow(Mo, off)
        elif cw:
            shallow = True
    if prev == 1 and is_w_col(pv) and closes_unit(nxt):
        pnt = off > 0 and par0(Mo, off - 1) == 0
        shallow = not (hi and not pnt)
    elif V13['wchain'] and prev == 1 and closes_unit(nxt):
        j = wchain_head(Mo, off)
        if j is not None and V14['h1'] and copy_head(Mo, j):
            j = None
        if j is not None:
            shallow = not (hi and not (par0(Mo, j) == 0))
    if closes_hi_unit(p, nxt, pv, pv2, hi, is_repeat(Mo, off)):
        shallow = True
    memo[k] = shallow
    return shallow
