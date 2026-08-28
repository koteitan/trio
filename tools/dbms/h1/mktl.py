# -*- coding: utf-8 -*-
"""H21: `top_level` に「親が `term_top`」を足す旗 rows3tl.py（TLFLAGS=tlterm,tlanch）。

群 B（`closes_top` の 3 件）の中身:
    接頭辞 = (0,0,0)(1,1,1)(2,X,Y)(1,1,0)(2,0,0)(3,1,1)(4,1,0)   site = 第 6 列
    M1 の次の柱 (2,0,0) … 親は**アンカー (1,1,0)** -> `top_level` False -> **deep**
    M2 の次の柱 (3,0,0) … 親は**写しの頭 (2,0,0)** -> `top_level` True  -> **shallow**
  ＝ 次の柱が**深い**ほうが浅く綴られる（反単調）。

`top_level` は「いまの写しの根の直下か」を
    親が根 `(0,*,*)` / 親が写しの頭 `copy_head`
で判定しているが、**アンカー (1,1,0) は行 1 の項の頭**（`term_top`）なので
「根の直下」に数えてよいはずである。足すと M1 側も True になって反転が消える。

  tlterm  `top_level` に `term_top(Mo, q)` を足す
  tlanch  `top_level` に「親がアンカー」だけを足す（より狭い）
"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = ("TL = {'tlterm': False, 'tlanch': False}\n"
        "for _k in os.environ.get('TLFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in TL, _k\n"
        "        TL[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
a = """    q = par0(Mo, j)
    return q < 0 or Mo[q][0] == 0 or copy_head(Mo, q)"""
b = """    q = par0(Mo, j)
    if q < 0 or Mo[q][0] == 0 or copy_head(Mo, q):
        return True
    if TL['tlterm'] and term_top(Mo, q):
        return True
    if TL['tlanch'] and tuple(Mo[q]) == ANCHOR:
        return True
    return False"""
assert src.count(a) == 1
src = src.replace(a, b, 1)
open('/tmp/h1work/rows3tl.py', 'w').write(src)
print('ok')
