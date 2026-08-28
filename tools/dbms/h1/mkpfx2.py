# -*- coding: utf-8 -*-
"""H19: `tie_sd` / `aw_flip` の門から「先を読むリテラル」を落とした版（rows3q.py）。

課題 R7 の順序保存の破れ 41 のうち **34 が `tiesd`、4 が `awflip`** に由来する
（`RS_NOTIESD=1` で 41 -> 7、さらに `RS_NOAWFLIP=1` で 3）。
どちらの門も H13 で足した「遠い素性」を使っていて、それが**行列の末尾**を読む:

    tie_sd  … `nx1_r1_lt`（次の柱の 行 1。無いときは -9 で真）
    aw_flip … `last_w`（**行列の末尾列**が「x w」か）/ `chead_after0`（後ろに写しの頭が無い）

PQFLAGS=tsd_pfx,awf_pfx
"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = ("PQ = {'tsd_pfx': False, 'awf_pfx': False, 'awf_off': False}\n"
        "for _k in os.environ.get('PQFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in PQ, _k\n"
        "        PQ[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
a = """    nx1 = Mo[off + 1][1] if off + 1 < len(Mo) else -9
    if not (nx1 < Mo[off][1]):
        return False
    return sum(1 for t in range(off) if Mo[t][2] > 0) >= 3"""
b = """    if not PQ['tsd_pfx']:
        nx1 = Mo[off + 1][1] if off + 1 < len(Mo) else -9
        if not (nx1 < Mo[off][1]):
            return False
    return sum(1 for t in range(off) if Mo[t][2] > 0) >= 3"""
assert src.count(a) == 1
src = src.replace(a, b, 1)
c = """    n = len(Mo)
    if is_w_col(Mo[-1]) and not any(copy_head(Mo, t) for t in range(off + 1, n)):
        return True"""
d = """    n = len(Mo)
    if PQ['awf_off']:
        return False
    if not PQ['awf_pfx']:
        if is_w_col(Mo[-1]) and not any(copy_head(Mo, t)
                                        for t in range(off + 1, n)):
            return True"""
assert src.count(c) == 1
src = src.replace(c, d, 1)
open('/tmp/h1work/rows3q.py', 'w').write(src)
print('ok')
