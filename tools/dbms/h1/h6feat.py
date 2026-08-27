# -*- coding: utf-8 -*-
"""H6 (2): 素性を機械生成する。行 0 / 行 1 / 行 2 の祖先の鎖、可変長の接尾辞など。
   どれも行列から直に読める（写しに同変）。"""
import sys
sys.path.insert(0,'/tmp/h1work'); sys.path.insert(0,'/home/koteitan/proofs/dbms/tools/dbms')
from rows3 import (is_branch, is_w_col, par0, hi_block, is_repeat, ANCHOR,
                   copy_head, term_top, top_level, closes_unit, wchain_head)

def par(m, x, k):
    """行 k の親: 左にある、行 k の値がより小さい直近の柱。無ければ -1。"""
    for q in range(x - 1, -1, -1):
        if m[q][k] < m[x][k]:
            return q
    return -1

def chain(m, x, k, n=3):
    """行 k の祖先の鎖（近い順に n 個）。届かないところは None。"""
    out, j = [], x
    for _ in range(n):
        j = par(m, j, k)
        out.append(j if j >= 0 else None)
        if j < 0: 
            out += [None] * (n - len(out)); break
    return out[:n]

def descend_end(m, x):
    """x の子孫がどこまで続くか（行 0 で x より深い柱が続く最後の添字 + 1）。"""
    j = x + 1
    while j < len(m) and m[j][0] > m[x][0]:
        j += 1
    return j

def next_term(m, x):
    """次の「項の頭」までの距離（term_top になる柱）。無ければ len(m)-x。"""
    for j in range(x + 1, len(m)):
        if term_top(m, j):
            return j - x
    return len(m) - x

def atoms(Mo, off, extra=None):
    n = len(Mo); p = tuple(Mo[off])
    g = lambda i: tuple(Mo[i]) if 0 <= i < n else None
    a = {}
    # --- 近傍（前後 3 本） -------------------------------------------
    for t in (-3,-2,-1,1,2,3):
        c = g(off + t); nm = ('pv%d' % -t) if t < 0 else ('nx%d' % t)
        a['%s_none' % nm] = c is None
        if c is None: c = (-9,-9,-9)
        for k,rn in ((0,'r0'),(1,'r1'),(2,'r2')):
            a['%s_%s_eq' % (nm,rn)] = c[k] == p[k]
            a['%s_%s_lt' % (nm,rn)] = c[k] < p[k]
            a['%s_%s_d1' % (nm,rn)] = c[k] == p[k] - 1
        a['%s_w' % nm] = c[1] == 0 and c[2] == 0 and c[0] >= 1
        a['%s_br' % nm] = c[1] == 1 and c[2] == 0 and c[0] >= 2
        a['%s_z' % nm] = c[2] > 0
    # --- 行 0 / 行 1 / 行 2 の祖先の鎖 -------------------------------
    for k,rn in ((0,'a0'),(1,'a1'),(2,'a2')):
        ch = chain(Mo, off, k, 3)
        for lv, j in enumerate(ch, 1):
            a['%s%d_none' % (rn,lv)] = j is None
            c = g(j) if j is not None else (-9,-9,-9)
            d = (off - j) if j is not None else -9
            a['%s%d_root' % (rn,lv)] = j == 0
            a['%s%d_adj' % (rn,lv)] = d == 1
            a['%s%d_far' % (rn,lv)] = d > 3
            a['%s%d_w' % (rn,lv)] = c[1] == 0 and c[2] == 0 and c[0] >= 1
            a['%s%d_anch' % (rn,lv)] = tuple(c) == ANCHOR
            a['%s%d_z' % (rn,lv)] = c[2] > 0
            a['%s%d_chead' % (rn,lv)] = j is not None and copy_head(Mo, j)
            a['%s%d_termtop' % (rn,lv)] = j is not None and term_top(Mo, j)
            for kk,rr in ((0,'r0'),(1,'r1'),(2,'r2')):
                a['%s%d_%s_d1' % (rn,lv,rr)] = c[kk] == p[kk] - 1
                a['%s%d_%s_eq' % (rn,lv,rr)] = c[kk] == p[kk]
    # --- 可変長の量 --------------------------------------------------
    de = descend_end(Mo, off); nt = next_term(Mo, off)
    a['desc0'] = de == off + 1
    a['desc_ge2'] = de - off - 1 >= 2
    a['desc_end'] = de == n
    a['nt1'] = nt == 1
    a['nt2'] = nt == 2
    a['nt_ge4'] = nt >= 4
    a['nt_end'] = off + nt >= n
    a['tail1'] = n - off == 1
    a['tail2'] = n - off == 2
    a['tail_ge6'] = n - off >= 6
    # --- 行 2 の構造（展開で変わらないので完全に同変） ----------------
    z_before = [t for t in range(off) if Mo[t][2] > 0]
    z_after = [t for t in range(off + 1, n) if Mo[t][2] > 0]
    a['z_before0'] = len(z_before) == 0
    a['z_before1'] = len(z_before) == 1
    a['z_before_ge3'] = len(z_before) >= 3
    a['z_after0'] = len(z_after) == 0
    a['z_after1'] = len(z_after) == 1
    a['z_after_ge3'] = len(z_after) >= 3
    a['z_last_adj'] = bool(z_before) and off - z_before[-1] <= 2
    a['z_last_far'] = bool(z_before) and off - z_before[-1] > 4
    a['z_next_adj'] = bool(z_after) and z_after[0] - off <= 2
    # --- 写しの構造 --------------------------------------------------
    ch_all = [t for t in range(n) if copy_head(Mo, t)]
    a['nchead0'] = len(ch_all) == 0
    a['nchead1'] = len(ch_all) == 1
    a['nchead_ge3'] = len(ch_all) >= 3
    a['chead_after0'] = not any(t > off for t in ch_all)
    a['chead_after1'] = sum(1 for t in ch_all if t > off) == 1
    a['chead_before0'] = not any(t < off for t in ch_all)
    a['chead_before1'] = sum(1 for t in ch_all if t < off) == 1
    a['chead_before2'] = sum(1 for t in ch_all if t < off) == 2
    # 写しのブロック長で見た位置
    if len(ch_all) >= 2:
        blk = ch_all[1] - ch_all[0]
        a['in_blk_head'] = any(0 <= off - t < 2 for t in ch_all)
        a['in_blk_tail'] = any(0 < t - off <= 2 for t in ch_all)
        a['blk_ge5'] = blk >= 5
    else:
        a['in_blk_head'] = a['in_blk_tail'] = a['blk_ge5'] = False
    # --- 既存の道具 --------------------------------------------------
    a['hi'] = hi_block(Mo, off)
    a['rep'] = is_repeat(Mo, off)
    a['wch'] = wchain_head(Mo, off) is not None
    a['anch_before'] = any(tuple(c) == ANCHOR for c in Mo[:off])
    a['p0_ge4'] = p[0] >= 4
    a['p0_ge6'] = p[0] >= 6
    # --- 行 2 の木（行 2 は展開で変わらないので完全に同変）------------
    # 分岐列は 行 2 = 0 なので `par(.,.,2)` は -1 になる。代わりに
    # 「直前の 行 2 > 0 の柱」を行 2 のブロックの頭として見る。
    zp = z_before[-1] if z_before else None
    a['zp_none'] = zp is None
    zc = g(zp) if zp is not None else (-9,-9,-9)
    a['zp_adj'] = zp is not None and off - zp == 1
    a['zp_d2'] = zp is not None and off - zp == 2
    a['zp_far'] = zp is not None and off - zp > 4
    a['zp_anc'] = zp is not None and zc[0] < p[0]      # 行 0 で自分の祖先か
    a['zp_r0_d1'] = zc[0] == p[0] - 1
    a['zp_r0_d2'] = zc[0] == p[0] - 2
    a['zp_r0_eq'] = zc[0] == p[0]
    a['zp_r1_eq'] = zc[1] == p[1]
    a['zp_r1_ge2'] = zc[1] >= 2
    a['zp_diag'] = zc[0] == zc[1] and zc[0] >= 1
    a['zp_par_root'] = zp is not None and par(Mo, zp, 0) == 0
    a['zp_par_chead'] = zp is not None and par(Mo, zp, 0) >= 0 and copy_head(Mo, par(Mo, zp, 0))
    a['zp_par_termtop'] = zp is not None and par(Mo, zp, 0) >= 0 and term_top(Mo, par(Mo, zp, 0))
    a['zp_termtop_up'] = zp is not None and any(term_top(Mo, t) for t in range(zp + 1, off))
    # 行 0 の祖先のうち 行 2 > 0 のものの本数（＝行 2 の深さ）
    anc0 = []
    j = off
    while True:
        j = par(Mo, j, 0)
        if j < 0: break
        anc0.append(j)
    a['zdepth0'] = sum(1 for t in anc0 if Mo[t][2] > 0) == 0
    a['zdepth1'] = sum(1 for t in anc0 if Mo[t][2] > 0) == 1
    a['zdepth_ge2'] = sum(1 for t in anc0 if Mo[t][2] > 0) >= 2
    # いまの「項」の中の 行 2 > 0 の本数
    th = 0
    for t in range(off - 1, -1, -1):
        if term_top(Mo, t): th = t; break
    a['zblk0'] = sum(1 for t in range(th, off) if Mo[t][2] > 0) == 0
    a['zblk1'] = sum(1 for t in range(th, off) if Mo[t][2] > 0) == 1
    a['zblk_ge2'] = sum(1 for t in range(th, off) if Mo[t][2] > 0) >= 2
    a['th_adj'] = off - th <= 1
    a['th_far'] = off - th > 4
    a['th_chead'] = copy_head(Mo, th)
    a['th_anch'] = tuple(Mo[th]) == ANCHOR
    a['th_root'] = Mo[th][0] == 0
    if extra:
        a.update(extra)
    return {k: bool(v) for k, v in a.items()}
