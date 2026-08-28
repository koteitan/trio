# -*- coding: utf-8 -*-
"""H11 の条項 `sibnb`: `sibL` が兄弟に渡す「深い側」を**分岐列以外**にも効かせる。

いまの `rows3.py` は

    if is_branch(p):  ... deep = base_sd ...      # 分岐列だけが base_sd を見る
    else:             base = base_d               # それ以外は素の梯子だけ

破れの 45/80 は**兄弟のアンカー (1,1,0)**（分岐列でない）が 1 段浅い。
そこで非分岐でも `base_sd` を使えるようにする旗を足す（既定 off = v14 と同じ）。

  SB['sibnb']      非分岐でも base_sd を使う
  SB['sibnb_anch'] 対象をアンカー (1,1,0) だけに絞る
  SB['sibnb_v1']   対象を v == 1 の柱だけに絞る
環境変数 SBFLAGS=sibnb,sibnb_anch のように指定する。
"""
import os
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", "FIRE = []\nSITES = [None]\n\n\nV12 = {", 1)
src = src.replace("V12 = {",
                  "SB = {'sibnb': False, 'sibnb_anch': False, 'sibnb_v1': False,\n"
                  "      'sibnb_nosrc': False, 'sibnb_cov': False,\n      'sibnb_cov2': False}\n"
                  "for _k in os.environ.get('SBFLAGS', '').split(','):\n"
                  "    if _k.strip():\n"
                  "        assert _k.strip() in SB, _k\n"
                  "        SB[_k.strip()] = True\n\n\nV12 = {", 1)
src = src.replace("def sib_ok(off, src, st):", '''def _parK(m, x, k):
    for q in range(x - 1, -1, -1):
        if m[q][k] < m[x][k]:
            return q
    return -1


def sibnb_cov(Mo, off):
    """H11 の集合被覆が出した 3 項の連言（正例 42/42, 偽陽性 0/410）。

        a01_far & !a01_r2_d1 & !a11_far
    """
    p = tuple(Mo[off])
    a01, a11 = _parK(Mo, off, 0), _parK(Mo, off, 1)
    c = tuple(Mo[a01]) if a01 >= 0 else (-9, -9, -9)
    return ((a01 >= 0 and off - a01 > 3)
            and not (c[2] == p[2] - 1)
            and not (a11 >= 0 and off - a11 > 3))


def sibnb_cov2(Mo, off):
    \"\"\"H11 の 2 巡目（負例を lim=7 の一致からも集めた）。

        !a11_far & nx1_z & th_far
          a11_far  行 1 の親が 4 本より遠い
          nx1_z    次の柱の 行 2 > 0
          th_far   いまの「項の頭」term_top が 4 本より遠い
    \"\"\"
    n = len(Mo)
    a11 = _parK(Mo, off, 1)
    if a11 >= 0 and off - a11 > 3:
        return False
    if not (off + 1 < n and Mo[off + 1][2] > 0):
        return False
    th = 0
    for t in range(off - 1, -1, -1):
        if term_top(Mo, t):
            th = t
            break
    return off - th > 4


def sib_ok(off, src, st):''', 1)
old = "    else:\n        base = base_d\n\n    lad1 = first1"
new = ("    else:\n"
       "        base = base_d\n"
       "        if (SB['sibnb'] and v >= 1 and base_sd != base_d\n"
       "                and not (SB['sibnb_anch'] and tuple(p) != ANCHOR)\n"
       "                and not (SB['sibnb_v1'] and v != 1)\n"
       "                and (SB['sibnb_nosrc'] or sib_ok(off, src, st))\n"
       "                and (SITES[0] is None or off in SITES[0])\n"
       "                and (not SB['sibnb_cov'] or sibnb_cov(st['Mo'], off))\n"
       "                and (not SB['sibnb_cov2'] or sibnb_cov2(st['Mo'], off))):\n"
       "            base = base_sd\n"
       "            FIRE.append((off, tuple(p), base_d, base_sd, src))\n\n    lad1 = first1")
assert src.count(old) == 1, src.count(old)
src = src.replace(old, new, 1)
src += '''

def b2d3f(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3s.py', 'w').write(src)
print('ok')
