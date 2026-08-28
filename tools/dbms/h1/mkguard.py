# -*- coding: utf-8 -*-
"""H13: 縮約の 2 つの門と rest2 の深さを数える写し rows3g2.py。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = "from collections import Counter\nGC = Counter()\nGEX = []\n\n\nV12 = {"
src = src.replace("V12 = {", HEAD, 1)
old = """            if rest2:
                if rest2[0][0] < p[0] + 1:
                    continue"""
new = """            if rest2:
                GC['rest2[0][0] - p[0] = %d' % (rest2[0][0] - p[0])] += 1
                GC['rest2 の先頭が最小' if rest2[0][0] == min(x[0] for x in rest2)
                   else '**rest2 の先頭が最小でない**'] += 1
                if rest2[0][0] - p[0] >= 2 and len(GEX) < 8:
                    GEX.append((tuple(st['Mo']), off, tuple(p), tuple(pre),
                                tuple(map(tuple, rest2)), tuple(Aq)))
                if rest2[0][0] < p[0] + 1:
                    GC['**門 rest2[0][0] < p[0]+1 が発火**'] += 1
                    continue"""
assert src.count(old) == 1
src = src.replace(old, new, 1)
open('/tmp/h1work/rows3g2.py', 'w').write(src)
print('ok')
