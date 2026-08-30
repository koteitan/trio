# -*- coding: utf-8 -*-
"""H23: クラス D / E の条項（v20 の上で、単調な素性だけで学習した門）rows3z.py。

  fD  いま shallow だが deep が正しい
      門 `(!a01_adj & !a11_root & !z_before1) | (!a11_root & after_unit_ge4)`
      （正例 10/10 / 負例 337, fp=0。素性は**単調なもの 290 本**だけ）
      `after_unit_ge4` は「後ろに柱が 4 本以上ある」＝ **上に閉じた**条件なので
      **deep 化に使ってよい向き**である（課題 H22 の教訓）。
  fE  tie で base_sd を使う（シート由来の負例は 0 本）
ZFLAGS=fD,fE
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
HEAD = ("ZF = {'fD': False, 'fE': False}\n"
        "for _k in os.environ.get('ZFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in ZF, _k\n"
        "        ZF[_k.strip()] = True\n"
        "FIRE = []\nSITES = [None]\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
GATE = '\n'.join([
 "def _afterunit(Mo, off):",
 "    n = len(Mo)",
 "    for j in range(off + 1, n):",
 "        if term_top(Mo, j):",
 "            return n - j",
 "    return 0",
 "",
 "",
 "def zD(Mo, off):",
 "    a01 = par0(Mo, off)",
 "    a11 = _parK(Mo, off, 1)",
 "    if a11 == 0:",
 "        return False",
 "    zb = sum(1 for t in range(off) if Mo[t][2] > 0)",
 "    if not (a01 >= 0 and off - a01 == 1) and zb != 1:",
 "        return True",
 "    return _afterunit(Mo, off) >= 4",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
a = "            base = base_s if shallow else deep"
b = ("            if (ZF['fD'] and shallow and zD(st['Mo'], off)\n"
     "                    and (SITES[0] is None or off in SITES[0])):\n"
     "                shallow = False\n"
     "                FIRE.append((off, tuple(p), 'D'))\n"
     "            base = base_s if shallow else deep")
assert src.count(a) == 1
src = src.replace(a, b, 1)
c = """            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep"""
d = """            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep
            if (ZF['fE'] and base_sd != deep
                    and (SITES[0] is None or off in SITES[0])):
                base = base_sd
                FIRE.append((off, tuple(p), 'E'))"""
assert src.count(c) == 1
src = src.replace(c, d, 1)
src += '''

def b2d3z(M, sites=None):
    SITES[0] = sites
    del FIRE[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    SITES[0] = None
    return out, list(FIRE)
'''
open('/tmp/h1work/rows3z.py', 'w').write(src)
print('ok')
