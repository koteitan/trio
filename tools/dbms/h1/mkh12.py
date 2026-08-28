# -*- coding: utf-8 -*-
"""H12: 証人から逆算した 3 つの条項を旗で入れ切りする写し rows3w.py。

  fA  いまは deep だが shallow が正しい     門 `a11_adj & !nt_end`
  fB  いまは shallow だが deep が正しい     門 `!a01_adj & !a11_root`
  fC  tie だが base_sd（兄弟の深い側）が正しい
環境変数 WFLAGS=fA,fB,fC
"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {",
                  "WF = {'fA': False, 'fB': False, 'fC': False}\n"
                  "for _k in os.environ.get('WFLAGS', '').split(','):\n"
                  "    if _k.strip():\n"
                  "        assert _k.strip() in WF, _k\n"
                  "        WF[_k.strip()] = True\n"
                  "FIRE = []\nSITES = [None]\n\n\nV12 = {", 1)

GATE = '\n'.join([
 "def _nextterm(Mo, off):",
 "    for j in range(off + 1, len(Mo)):",
 "        if term_top(Mo, j):",
 "            return j - off",
 "    return len(Mo) - off",
 "",
 "",
 "def h12_A(Mo, off):",
 "    # a11_adj & !nt_end   (fp=0, 正例 14/14 / 負例 2170)",
 "    a11 = _parK(Mo, off, 1)",
 "    if not (a11 >= 0 and off - a11 == 1):",
 "        return False",
 "    return off + _nextterm(Mo, off) < len(Mo)",
 "",
 "",
 "def h12_B(Mo, off):",
 "    # !a01_adj & !a11_root   (fp=0, 正例 10/10 / 負例 336)",
 "    a01 = _parK(Mo, off, 0)",
 "    if a01 >= 0 and off - a01 == 1:",
 "        return False",
 "    return _parK(Mo, off, 1) != 0",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)

old = "            base = base_s if shallow else deep"
new = ("            Mo2 = st['Mo']\n"
       "            if WF['fA'] and not shallow and h12_A(Mo2, off) and (\n"
       "                    SITES[0] is None or off in SITES[0]):\n"
       "                shallow = True\n"
       "                FIRE.append((off, tuple(p), 'A'))\n"
       "            elif WF['fB'] and shallow and h12_B(Mo2, off) and (\n"
       "                    SITES[0] is None or off in SITES[0]):\n"
       "                shallow = False\n"
       "                FIRE.append((off, tuple(p), 'B'))\n"
       "            base = base_s if shallow else deep")
assert src.count(old) == 1
src = src.replace(old, new, 1)

old2 = """            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep"""
new2 = """            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep
            if (WF['fC'] and base_sd != deep
                    and (SITES[0] is None or off in SITES[0])):
                base = base_sd
                FIRE.append((off, tuple(p), 'C'))"""
assert src.count(old2) == 1
src = src.replace(old2, new2, 1)

src += '''

def b2d3w(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3w.py', 'w').write(src)
print('ok')
