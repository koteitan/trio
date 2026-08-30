"""rows3.conv3 の写し（分岐列の決定を丸ごと記録する版）。/tmp/h1work/provh.py を作る。"""
SRC = '/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py'
OUT = '/tmp/h1work/provh.py'
lines = open(SRC).read().split('\n')
i0 = next(i for i, l in enumerate(lines) if l.startswith('def conv3('))
i1 = next(i for i, l in enumerate(lines) if l.startswith('def b2d3n('))
body = '\n'.join(lines[i0:i1])

REPL = [
    ("    src = None\n",
     "    src = None\n    why = None\n    dec = None\n"),
    ("        cols.append((d, pw[0], pw[1]))\n",
     "        cols.append((d, pw[0], pw[1]))\n"
     "        PROV.append(('sh0', off, why, tuple(CTX), dec))\n"),
    ("        cols.append((dd, base, pl2))\n",
     "        cols.append((dd, base, pl2))\n"
     "        PROV.append(('sh1', off, why, tuple(CTX), dec))\n"),
    ("    cols.append((dd, e1, e2))\n",
     "    cols.append((dd, e1, e2))\n"
     "    PROV.append(('body', off, why, tuple(CTX), dec))\n"),
    ("            shallow = (st['prev'] == 0) or closes_unit(nxt)\n",
     "            shallow = (st['prev'] == 0) or closes_unit(nxt)\n"
     "            _prev0 = st['prev']\n"
     "            why = ('prev0' if st['prev'] == 0 else\n"
     "                   ('closes' if closes_unit(nxt) else 'plain'))\n"),
    ("                shallow = not (hi and not pnt)\n",
     "                shallow = not (hi and not pnt)\n"
     "                why = 'after_w'\n"),
    ("                    shallow = not (hi and not (par0(Mo, j) == 0))\n",
     "                    shallow = not (hi and not (par0(Mo, j) == 0))\n"
     "                    why = 'wchain'\n"),
    ("                shallow = True\n            base = base_s if shallow else deep\n",
     "                shallow = True\n"
     "                why = (why or '?') + '+closes_hi'\n"
     "            base = base_s if shallow else deep\n"
     "            dec = dict(prev0=_prev0, shallow=shallow, base_s=base_s,\n"
     "                       deep=deep, base_d=base_d, base_sd=base_sd,\n"
     "                       nxt=(tuple(nxt) if nxt is not None else None),\n"
     "                       onx=(tuple(onx) if onx is not None else None),\n"
     "                       hi=hi, why=None)\n"
     "            why = (why or '?') + ('/shallow' if shallow else '/deep')\n"
     "            dec['why'] = why\n"),
    ("            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い\n",
     "            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い\n"
     "            why = 'tie'\n"
     "            dec = dict(prev0=st['prev'], shallow=None, base_s=base_s,\n"
     "                       deep=deep, base_d=base_d, base_sd=base_sd,\n"
     "                       nxt=(tuple(nxt) if nxt is not None else None),\n"
     "                       onx=None, hi=None, why='tie')\n"),
]
CTXR = [
    ("            cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,\n"
     "                       U[0] if U else na, oA)\n",
     "            CTX.append('cA')\n"
     "            cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, False, st,\n"
     "                       U[0] if U else na, oA)\n"
     "            CTX.pop()\n"),
    ("            cU = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,\n"
     "                       oU)\n",
     "            CTX.append('cU')\n"
     "            cU = conv3(U, d + 1, L, FA, (v, s2), (e1, e2), False, False, st, na,\n"
     "                       oU)\n"
     "            CTX.pop()\n"),
    ("            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)\n",
     "            CTX.append('cR')\n"
     "            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)\n"
     "            CTX.pop()\n"),
    ("            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,\n"
     "                       oBq)\n",
     "            CTX.append('cB')\n"
     "            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,\n"
     "                       oBq)\n"
     "            CTX.pop()\n"),
]
for a, b in REPL + CTXR:
    assert body.count(a) == 1, ('miss', a[:60], body.count(a))
    body = body.replace(a, b)

head = ('"""分岐列の決定を丸ごと記録する conv3 の写し（mkprovh.py が生成）。"""\n'
        'import sys\n'
        "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')\n"
        'from rows3 import (split0, Lat, padL, is_branch, is_w_col, par0,\n'
        '                   hi_block, is_repeat, closes_unit, closes_hi_unit,\n'
        '                   wchain_head, sib_ok, ok_place, fit, dmap_at,\n'
        '                   units_split, contrPre, leaves_mark,\n'
        '                   leaves_mark_local, ANCHOR, NOTLAST, V12, V13, V14)\n'
        'PROV = []\n'
        'CTX = []\n\n\n')
tail = '''

def b2d3p(M):
    del PROV[:]
    del CTX[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
          'rec': {}}
    out = tuple(conv3(list(M), st=st))
    assert len(out) == len(PROV), (len(out), len(PROV))
    return out, list(PROV)
'''
open(OUT, 'w').write(head + body + tail)
print('wrote', OUT)
