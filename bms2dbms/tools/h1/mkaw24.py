# -*- coding: utf-8 -*-
"""H24: `after_w` の出力を強制する旗 rows3aw.py（AWFLAGS=awdeep,awshal,awnone）。

v20 の濃縮表で「**`/shallow` で決めた**」が破れの 40.5%（濃縮 28 倍）。
`after_w` が shallow を出すのをやめたらどうなるかを測る。
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
HEAD = ("AW = {'awdeep': False, 'awshal': False, 'awnone': False}\n"
        "for _k in os.environ.get('AWFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in AW, _k\n"
        "        AW[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
a = """                pnt = off > 0 and _p0(Mo, off - 1) == 0
                shallow = not (hi and not pnt)"""
b = """                pnt = off > 0 and _p0(Mo, off - 1) == 0
                _s0 = shallow
                shallow = not (hi and not pnt)
                if AW['awdeep']:
                    shallow = False
                elif AW['awshal']:
                    shallow = True
                elif AW['awnone']:
                    shallow = _s0"""
assert src.count(a) == 1
src = src.replace(a, b, 1)
open('/tmp/h1work/rows3aw.py', 'w').write(src)
print('ok')
