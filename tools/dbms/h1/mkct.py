# -*- coding: utf-8 -*-
"""H19: `closes_top` だけを切る旗 rows3ct.py（CTFLAGS=noct,noct2,nop0）。

`RS_NOH1=1` は H1 の 5 条項をまとめて切ってしまうので、1 つずつ切れる版を作る。
  noct  `closes_top` の枝（`elif cw: shallow = True`）を切る
  nop0  `p0_shallow`（prev==0 の枝。nxt を読む）を H1 前の 3 段重ねに戻す
"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = ("CT = {'noct': False, 'nop0': False}\n"
        "for _k in os.environ.get('CTFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in CT, _k\n"
        "        CT[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
a = """                elif cw:
                    shallow = True"""
b = """                elif cw and not CT['noct']:
                    shallow = True"""
assert src.count(a) == 1
src = src.replace(a, b, 1)
c = """                    _w0 = not p0_shallow(Mo, off)
                    shallow = not _w0"""
d = """                    if not CT['nop0']:
                        _w0 = not p0_shallow(Mo, off)
                        shallow = not _w0"""
assert src.count(c) == 1
src = src.replace(c, d, 1)
open('/tmp/h1work/rows3ct.py', 'w').write(src)
print('ok')
