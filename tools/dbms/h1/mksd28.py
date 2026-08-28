# -*- coding: utf-8 -*-
"""H28: `tie_sd` に第 2 の門を足す旗 rows3s2.py（SDFLAGS=sd2,sd2only）。

順序の縛りが外れたので **368 素性ぜんぶ**で学習し直した門:
    `!nchead_ge3 & nx1_r1_lt & pv2_r0_d1`   （正例 5/5 / 負例 12000, fp=0）
`nx1_r1_lt` は反単調なので H23 では使えなかったもの。
"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = ("SD = {'sd2': False, 'sd2only': False}\n"
        "for _k in os.environ.get('SDFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in SD, _k\n"
        "        SD[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
GATE = '\n'.join([
 "def tie_sd2(Mo, off):",
 "    # H28: !nchead_ge3 & nx1_r1_lt & pv2_r0_d1（正例 5/5 / 負例 12000, fp=0）",
 "    n = len(Mo)",
 "    if sum(1 for t in range(n) if copy_head(Mo, t)) >= 3:",
 "        return False",
 "    nx1 = Mo[off + 1][1] if off + 1 < n else -9",
 "    if not (nx1 < Mo[off][1]):",
 "        return False",
 "    pv2 = Mo[off - 2][0] if off >= 2 else -9",
 "    return pv2 == Mo[off][0] - 1",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
a = """            if (V18['tiesd'] and base_sd != deep
                    and tie_sd(st['Mo'], off)):
                base = base_sd"""
b = """            if (V18['tiesd'] and base_sd != deep
                    and ((tie_sd(st['Mo'], off) and not SD['sd2only'])
                         or (SD['sd2'] and tie_sd2(st['Mo'], off)))):
                base = base_sd"""
assert src.count(a) == 1
src = src.replace(a, b, 1)
open('/tmp/h1work/rows3s2.py', 'w').write(src)
print('ok')
