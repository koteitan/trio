# -*- coding: utf-8 -*-
"""H20: 条項の**向き**を制限する旗 rows3dn.py（DNFLAGS=awdown,ctdown）。

課題 H20 の診断:
  `aw_flip` は `last_w` が「続きが大きくなると真->偽」なのに **deep 化**に使っている
  `closes_top` は「続きが大きくなると偽->真」なのに **shallow 化**に使っている
  ⟹ どちらも向きが逆。減（＝ 順序の逆転）を作る。

  awdown  `aw_flip` を「deep -> shallow」の向きだけに使う
  ctdown  `closes_top` を「shallow -> deep」の向きだけに使う（＝ 事実上切る）
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
HEAD = ("DN = {'awdown': False, 'ctdown': False}\n"
        "for _k in os.environ.get('DNFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in DN, _k\n"
        "        DN[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
a = """                if V17['awflip'] and aw_flip(Mo, off):
                    shallow = not shallow"""
b = """                if V17['awflip'] and aw_flip(Mo, off) and not (
                        DN['awdown'] and shallow):
                    shallow = not shallow"""
assert src.count(a) == 1
src = src.replace(a, b, 1)
c = """                elif cw:
                    shallow = True"""
d = """                elif cw and not DN['ctdown']:
                    shallow = True"""
assert src.count(c) == 1
src = src.replace(c, d, 1)
open('/tmp/h1work/rows3dn.py', 'w').write(src)
print('ok')
