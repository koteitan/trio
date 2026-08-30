# -*- coding: utf-8 -*-
"""H12: 分岐列の「浅い／深い」を site ごとに強制できる写し rows3v.py。

    FORCE  {off: shallow}   その添字の決定を上書きする
    SLOG   [(off, shallow, base_s, deep, tie)]   決定の記録

`tie`（base_s == deep で選択肢が無い）も記録する。tie の site は
`deep` を `base_sd`（兄弟から来た深い側）に取り替えれば選択肢が生まれるので、
`FORCE[off] = 'sd'` でそれを試せるようにする。
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {", "FORCE = {}\nSLOG = []\n\n\nV12 = {", 1)

old = """            base = base_s if shallow else deep"""
new = """            if off in FORCE:
                shallow = FORCE[off]
            SLOG.append((off, bool(shallow), base_s, deep, base_sd, False))
            base = base_s if shallow else deep"""
assert src.count(old) == 1
src = src.replace(old, new, 1)

old2 = """        else:
            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            base = deep"""
new2 = """        else:
            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い
            SLOG.append((off, None, base_s, deep, base_sd, True))
            base = base_sd if FORCE.get(off) == 'sd' else deep"""
assert src.count(old2) == 1
src = src.replace(old2, new2, 1)

src += '''

def b2d3v(M, force=None):
    """(像, SLOG) の対。`force` は {off: shallow} / {off: 'sd'}。"""
    FORCE.clear()
    if force:
        FORCE.update(force)
    del SLOG[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0, 'rec': {}}
    out = tuple(conv3(list(M), st=st))
    FORCE.clear()
    return out, list(SLOG)
'''
open('/tmp/h1work/rows3v.py', 'w').write(src)
print('ok')
