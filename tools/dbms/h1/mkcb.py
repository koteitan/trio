# -*- coding: utf-8 -*-
"""H15: 縮約の兄弟の再帰 `cB` に渡す梯子を `L` -> `LS` にする旗（rows3c2.py）。

非縮約の枝は `cB = conv3(B, d, LS, ...)`（`sibL` の第 5/6 要素つき）を渡すのに、
縮約の枝は `cB = conv3(Bq, d, L, ...)` と**素の `L`** を渡している。
＝ 縮約の兄弟だけ `sibL` を受け取れない。H11 の `sibnb` と同じ形の穴。
CBFLAGS=cbls,cbfa
"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = ("CB = {'cbls': False, 'cbfa': False, 'cbfirst': False}\n"
        "for _k in os.environ.get('CBFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in CB, _k\n"
        "        CB[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
old = """            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
new = """            cB = conv3(Bq, d, LS if CB['cbls'] else L,
                       FA if CB['cbfa'] else FA,
                       (v, s2), (e1, e2),
                       first_of(st['Mo'], oBq) if CB['cbfirst'] else False,
                       False, st, nx, oBq)"""
assert src.count(old) == 1
src = src.replace(old, new, 1)
open('/tmp/h1work/rows3c2.py', 'w').write(src)
print('ok')
