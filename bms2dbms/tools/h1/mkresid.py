# -*- coding: utf-8 -*-
"""H12: `conv_resid` が渡す値を行列読みに差し替える旗つきの写し rows3r.py。

    out += conv3(head, rd, Lr, (False,)*12, ps, pw, False, False, st, nx2, off)
                      ^^   ^^  ^^^^^^^^^^^  ^^  ^^  ^^^^^
旗（環境変数 RFLAGS=a,b,c）:
  rfirst   first を `first_mat(Mo, off)`（行 0 の親の第 1 子か）にする
  rps      ps を `ps_mat(Mo, off)`（行 0 の親の (行1,行2)）にする
  rF       F を「行列から読んだ first1」にする（下の `F_mat`）
  rdmap    rd の `dmap_at` を使わず、写しに同変な深さ読みにする
"""
import os
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {",
                  "RF = {'rfirst': False, 'rps': False, 'rF': False, 'rdmap': False}\n"
                  "for _k in os.environ.get('RFLAGS', '').split(','):\n"
                  "    if _k.strip():\n"
                  "        assert _k.strip() in RF, _k\n"
                  "        RF[_k.strip()] = True\n\n\nV12 = {", 1)

# --- 行列読みの述語
anchor = "def _snap(st):"
assert src.count(anchor) == 1
src = src.replace(anchor, '''def first_mat(Mo, j):
    """`j` が行 0 の親の第 1 子か（＝ conv3 の `first` の行列読み）。"""
    return j == 0 or par0(Mo, j) == j - 1


def ps_mat(Mo, j):
    """`j` の行 0 の親の (行1, 行2)（＝ conv3 の `ps` の行列読み）。"""
    i = par0(Mo, j)
    return (0, 0) if i < 0 else (Mo[i][1], Mo[i][2])


''' + anchor, 1)

old = """        out += conv3(head, rd, Lr, (False,) * 12, ps, pw, False, False,
                     st, nx2, off)"""
new = """        Mo = st['Mo']
        _fi = first_mat(Mo, off) if RF['rfirst'] else False
        _ps = ps_mat(Mo, off) if RF['rps'] else ps
        _F = () if RF['rF'] else (False,) * 12
        out += conv3(head, rd, Lr, _F, _ps, pw, _fi, False,
                     st, nx2, off)"""
assert src.count(old) == 1
src = src.replace(old, new, 1)
open('/tmp/h1work/rows3r.py', 'w').write(src)
print('ok')

# ---------------------------------------------------------------- sib_ok の窓
# `sib_anchbefore` は「`off` より前にアンカー (1,1,0) が 1 本でもあるか」。
# 展開するとアンカーは写しの中で (k,1,0) に化けるので、**もとのアンカー 1 本で
# 以降の写し全部で門が閉じる**。＝ 写しに同変でない読み（H1 の族 α と同じ形）。
src2 = open('/tmp/h1work/rows3r.py').read()
src2 = src2.replace("RF = {'rfirst': False, 'rps': False, 'rF': False, 'rdmap': False}",
                    "RF = {'rfirst': False, 'rps': False, 'rF': False, 'rdmap': False,\n"
                    "      'sanchhead': False, 'sanchsrc': False, 'sanchterm': False,\n"
                    "      'sanchnone': False}")
old = """    if V13['sib_anchbefore']:
        Mo = st['Mo']
        if any(tuple(Mo[j]) == ANCHOR for j in range(0, off)):
            return False
    return True"""
new = """    if V13['sib_anchbefore']:
        Mo = st['Mo']
        lo = 0
        if RF['sanchhead']:
            # H1 の `hi_block2` と同じ手: 窓の頭を**いまの写しの頭**まで進める
            for j in range(off - 1, -1, -1):
                if copy_head(Mo, j):
                    lo = j
                    break
        elif RF['sanchsrc'] and src is not None:
            lo = src
        if RF['sanchnone']:
            hi = len(Mo)
        else:
            hi = off
        if RF['sanchterm']:
            if any(term_top(Mo, j) and Mo[j][0] >= 1 for j in range(lo, hi)):
                return False
        elif any(tuple(Mo[j]) == ANCHOR for j in range(lo, hi)):
            return False
    return True"""
assert src2.count(old) == 1
src2 = src2.replace(old, new, 1)
open('/tmp/h1work/rows3r.py', 'w').write(src2)
print('sib_ok の旗も足した')

# ---------------------------------------------------------------- 深さの読み
# 逆算（`h12b.py`）でわかったこと: 残余の中の「x w」柱 (k,0,0) が 1 段浅い。
#   B = (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(3,1,1)**(3,0,0)**(4,1,1)
#   T[7] = (5,0,0)   conv3(B)[7] = (4,0,0)
# (5,0,0) は「もとの深さ 3 の直前の柱（3,1,1）の本体の像の深さ」= dmap[3]。
src3 = open('/tmp/h1work/rows3r.py').read()
src3 = src3.replace("      'sanchnone': False}",
                    "      'sanchnone': False,\n"
                    "      'wdmap': False, 'wdmap_all': False, 'wdmap_w': False,\n"
                    "      'wd_deep': False, 'wd_notroot': False, 'wd_chead': False,\n"
                    "      'sbody': False, 'sbody_w': False, 'sb_gate': False,\n"
                    "      'sb_p0ge2': False, 'sb_notroot': False, 'sb_chead': False,\n"
                    "      'sb_cov': False}")
# (a) wdmap: 「x w」柱の深さを dmap（もとの深さ -> 像の深さ）で下限を付ける
old = """    ST = st['ST']
    cols = []"""
new = """    if (RF['wdmap'] and not first and p[0] >= 1
            and (RF['wdmap_all'] or (v == 0 and s2 == 0))
            and (not RF['wdmap_w'] or is_w_col(p))
            and (not RF['wd_deep'] or p[0] >= 2)
            and (not RF['wd_notroot'] or par0(st['Mo'], off) != 0)
            and (not RF['wd_chead'] or copy_head(st['Mo'], off))):
        # もとの深さ p[0] にすでに像の深さが決まっているなら、そこより浅く
        # 置かない（＝ 同じもとの深さの兄弟は像でも同じ深さに並ぶ）
        if st['dmap']:
            d = max(d, dmap_at(st, p[0]))

    ST = st['ST']
    cols = []"""
assert src3.count(old) == 1
src3 = src3.replace(old, new, 1)
# (b) sbody: 行 1 の影を立てた柱の兄弟を本体の横（dd）に付ける
old2 = "    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)"
new2 = ("    dB = d\n"
        "    if (RF['sbody'] and lad1 and B and dd > d\n"
        "            and (not RF['sbody_w'] or (B[0][1] == 0 and B[0][2] == 0))\n"
        "            and (SITES[0] is None or off in SITES[0])\n"
        "            and (not RF['sb_gate'] or sb_gate(st['Mo'], off))):\n"
        "        FIRE.append((off, tuple(p), d, dd, tuple(B[0])))\n"
        "        dB = dd\n"
        "    cB = conv3(B, dB, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)")
assert src3.count(old2) == 1
src3 = src3.replace(old2, new2, 1)
open('/tmp/h1work/rows3r.py', 'w').write(src3)
print('深さの旗も足した')

GATE = "def _nA(Mo, off):\n    j = off + 1\n    while j < len(Mo) and Mo[j][0] > Mo[off][0]:\n        j += 1\n    return j - off - 1\n\n\ndef sb_gate(Mo, off):\n    # H12: sbody の門（影の兄弟を本体の横に付けてよいか）\n    if RF['sb_p0ge2'] and Mo[off][0] < 2:\n        return False\n    if RF['sb_notroot'] and par0(Mo, off) == 0:\n        return False\n    if RF['sb_chead'] and not copy_head(Mo, off + 1 + _nA(Mo, off)):\n        return False\n    if RF['sb_cov'] and not sb_cov(Mo, off):\n        return False\n    return True\n\n\ndef sb_cov(Mo, off):\n    return True\n\n\n"

# ---------------------------------------------------------------- 発火の記録
src3b = open('/tmp/h1work/rows3r.py').read()
src3b = src3b.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
open('/tmp/h1work/rows3r.py', 'w').write(src3b)

src4 = open('/tmp/h1work/rows3r.py').read()
src4 = src4.replace("RF = {'rfirst'", "FIRE = []\nSITES = [None]\n\n\nRF = {'rfirst'", 1)
old = """        if st['dmap']:
            d = max(d, dmap_at(st, p[0]))"""
new = """        if st['dmap'] and dmap_at(st, p[0]) > d and (
                SITES[0] is None or off in SITES[0]):
            FIRE.append((off, tuple(p), d, dmap_at(st, p[0])))
            d = dmap_at(st, p[0])"""
assert src4.count(old) == 1
src4 = src4.replace(old, new, 1)
src4 += '''

def b2d3f(M, sites=None):
    """(像, FIRE) の対。`sites` を渡すとその添字でしか発火しない。"""
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3r.py', 'w').write(src4)
print('発火の記録も足した')
