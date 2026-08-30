# -*- coding: utf-8 -*-
"""H13: `after_w` の決定を旗で動かす写し rows3a.py（AFLAGS=...）。

  awinv    after_w が出した shallow を反転する
  awoff    after_w の枝を丸ごと切る（前の規則の shallow を残す）
  awdeep   after_w のときは必ず deep
  awshal   after_w のときは必ず shallow
  awgate   `aw_gate(Mo, off)` が真の site だけ反転する（学習した門）
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
HEAD = ("AF = {'awinv': False, 'awoff': False, 'awdeep': False, 'awshal': False,\n"
        "      'awgate': False, 'awgate1': False, 'awgate2': False, 'awgate3': False, 'awgate4': False}\n"
        "for _k in os.environ.get('AFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in AF, _k\n"
        "        AF[_k.strip()] = True\n"
        "FIRE = []\nSITES = [None]\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
GATE = '\n'.join([
 "def _nextterm_list(Mo, off):",
 "    return [j for j in range(off + 1, len(Mo)) if term_top(Mo, j)]",
 "",
 "",
 "def aw_gate(Mo, off):",
 "    # H13: 証人が要求する after_w の反転 22 本を fp=0 で覆う 3 選言",
 "    #   last_r1_lt              行列の**末尾列**の 行 1 が この柱より小さい (14/22)",
 "    #   !a01_far & !hi & rep    (6/22)",
 "    #   !hi & !last_r1_eq       (2/22)",
 "    p = Mo[off]",
 "    L = Mo[-1]",
 "    if L[1] < p[1]:",
 "        return True",
 "    hi = hi_block2(Mo, off) if V14['h1'] else hi_block(Mo, off)",
 "    a01 = par0(Mo, off)",
 "    if (not (a01 >= 0 and off - a01 > 3)) and (not hi) and is_repeat(Mo, off):",
 "        return True",
 "    if (not hi) and L[1] != p[1]:",
 "        return True",
 "    return False",
 "",
 "",
 "def aw_gate1(Mo, off):",
 "    return Mo[-1][1] < Mo[off][1]",
 "",
 "",
 "def _afterunit(Mo, off):",
 "    n = len(Mo)",
 "    nt = n",
 "    for j in range(off + 1, n):",
 "        if term_top(Mo, j):",
 "            nt = j",
 "            break",
 "    return n - nt",
 "",
 "",
 "def _sibdiag(Mo, off):",
 "    p0 = Mo[off][0]",
 "    for t in range(off - 1, -1, -1):",
 "        if Mo[t][0] < p0:",
 "            return False",
 "        if Mo[t][0] == p0:",
 "            return Mo[t][0] == Mo[t][1] and Mo[t][0] >= 1",
 "    return False",
 "",
 "",
 "def aw_gate2(Mo, off):",
 "    # H13 2 巡目: after_unit_ge8 & last_r1_lt  (fp=0, 14/22 / 負例 921)",
 "    return _afterunit(Mo, off) >= 8 and Mo[-1][1] < Mo[off][1]",
 "",
 "",
 "def aw_gate4(Mo, off):",
 "    # H13 3 巡目: (chead_after0 & last_w) | (!a01_far & x_sib_diag)",
 "    #   fp=0, 18/22 / 負例 924",
 "    if is_w_col(Mo[-1]) and not any(copy_head(Mo, t)",
 "                                    for t in range(off + 1, len(Mo))):",
 "        return True",
 "    a01 = par0(Mo, off)",
 "    return (not (a01 >= 0 and off - a01 > 3)) and _sibdiag(Mo, off)",
 "",
 "",
 "def aw_gate3(Mo, off):",
 "    # 上に `!a01_far & x_sib_diag` を足した 2 選言 (18/22)",
 "    if aw_gate2(Mo, off):",
 "        return True",
 "    a01 = par0(Mo, off)",
 "    return (not (a01 >= 0 and off - a01 > 3)) and _sibdiag(Mo, off)",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
old = """            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)"""
new = """            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):
                pnt = off > 0 and _p0(Mo, off - 1) == 0
                _sh0 = shallow
                shallow = not (hi and not pnt)
                if SITES[0] is None or off in SITES[0]:
                    _new = shallow
                    if AF['awoff']:
                        _new = _sh0
                    elif AF['awdeep']:
                        _new = False
                    elif AF['awshal']:
                        _new = True
                    elif (AF['awinv'] or (AF['awgate'] and aw_gate(Mo, off))\n                          or (AF['awgate1'] and aw_gate1(Mo, off))\n                          or (AF['awgate2'] and aw_gate2(Mo, off))\n                          or (AF['awgate3'] and aw_gate3(Mo, off))\n                          or (AF['awgate4'] and aw_gate4(Mo, off))):
                        _new = not shallow
                    if _new != shallow:
                        FIRE.append((off, tuple(p), shallow, _new))
                    shallow = _new"""
assert src.count(old) == 1
src = src.replace(old, new, 1)
src += '''

def b2d3a(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3a.py', 'w').write(src)
print('ok')
