# -*- coding: utf-8 -*-
"""H14: クラス D / E の条項を旗で入れ切りする写し rows3d.py（DFLAGS=fD,fE）。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = ("DF = {'fD': False, 'fE': False, 'gDoff': False, 'gEoff': False}\n"
        "for _k in os.environ.get('DFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in DF, _k\n"
        "        DF[_k.strip()] = True\n"
        "FIRE = []\nSITES = [None]\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
GATE = '\n'.join([
 "def _zbefore(Mo, off):",
 "    return sum(1 for t in range(off) if Mo[t][2] > 0)",
 "",
 "",
 "def _afterunit0(Mo, off):",
 "    for j in range(off + 1, len(Mo)):",
 "        if term_top(Mo, j):",
 "            return False",
 "    return True",
 "",
 "",
 "def _nextunitcopy(Mo, off):",
 "    n = len(Mo)",
 "    th = 0",
 "    for j in range(off - 1, -1, -1):",
 "        if term_top(Mo, j):",
 "            th = j",
 "            break",
 "    nt = n",
 "    for j in range(off + 1, n):",
 "        if term_top(Mo, j):",
 "            nt = j",
 "            break",
 "    if nt >= n or nt - th > n - nt:",
 "        return False",
 "    d0 = Mo[nt][0] - Mo[th][0]",
 "    return all(Mo[nt + i][0] - Mo[th + i][0] == d0 and",
 "               Mo[nt + i][2] == Mo[th + i][2] for i in range(nt - th))",
 "",
 "",
 "def _f1anch(Mo, off):",
 "    for j in range(off + 1, len(Mo)):",
 "        if term_top(Mo, j):",
 "            return tuple(Mo[j]) == ANCHOR",
 "    return False",
 "",
 "",
 "def gD(Mo, off):",
 "    # H14 クラス D 4 巡目（正例 5/5, 負例 10601, fp=0）",
 "    #   (!a11_termtop & f1_anch & next_unit_copy) | (a11_adj & last_r1_gt)",
 "    a11 = _parK(Mo, off, 1)",
 "    if not (a11 >= 0 and term_top(Mo, a11)) and _f1anch(Mo, off) \\",
 "            and _nextunitcopy(Mo, off):",
 "        return True",
 "    if DF['gDoff']:",
 "        return False",
 "    return (a11 >= 0 and off - a11 == 1) and Mo[-1][1] > Mo[off][1]",
 "",
 "",
 "def gE(Mo, off):",
 "    # H14 クラス E 2 巡目（正例 4/5, 負例 9922, fp=0）",
 "    #   !a01_chead & nx1_r1_lt & z_before_ge3",
 "    a01 = par0(Mo, off)",
 "    if a01 >= 0 and copy_head(Mo, a01):",
 "        return False",
 "    nx1 = Mo[off + 1][1] if off + 1 < len(Mo) else -9",
 "    if not (nx1 < Mo[off][1]):",
 "        return False",
 "    return sum(1 for t in range(off) if Mo[t][2] > 0) >= 3",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
old = "            base = base_s if shallow else deep"
new = ("            if (DF['fD'] and shallow and not DF['gDoff']\n"
       "                    and gD(st['Mo'], off)\n"
       "                    and (SITES[0] is None or off in SITES[0])):\n"
       "                shallow = False\n"
       "                FIRE.append((off, tuple(p), 'D'))\n"
       "            base = base_s if shallow else deep")
assert src.count(old) == 1
src = src.replace(old, new, 1)
old2 = """            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep"""
new2 = """            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep
            if (DF['fE'] and base_sd != deep and gE(st['Mo'], off)
                    and (SITES[0] is None or off in SITES[0])):
                base = base_sd
                FIRE.append((off, tuple(p), 'E'))"""
assert src.count(old2) == 1
src = src.replace(old2, new2, 1)
src += '''

def b2d3d(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3d.py', 'w').write(src)
print('ok')
