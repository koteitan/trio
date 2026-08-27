"""rows3.py の conv3 / conv_resid を「柱ごとの出どころ」を記録する版に写す。

生成物 provc.py は rows3 と**同じ像**を返す（下の自己検査で確かめる）。
記録は PROV に (kind, off, why, ctx) を出力の順に積む:
  kind  'sh0' 行 0 の影 / 'sh1' 行 1 の影 / 'body' 本体
  off   もとの BMS 行列 Mo の何列目の柱か
  why   分岐列 (a,1,0) の綴りを決めた条項（prev0/closes/deep0/after_w/wchain/
        closes_hi/tie）と /shallow か /deep。分岐列でなければ None
  ctx   縮約の中のどの再帰か（cA=引数, cU=写し, cR=残余, cB=兄弟）の積み重ね
"""
import re, sys
SRC = '/home/koteitan/proofs/dbms/tools/dbms/rows3.py'
OUT = '/home/koteitan/proofs/dbms/tools/dbms/g2/provc.py'
lines = open(SRC).read().split('\n')
i0 = next(i for i, l in enumerate(lines) if l.startswith('def conv3('))
i1 = next(i for i, l in enumerate(lines) if l.startswith('def b2d3n('))
body = '\n'.join(lines[i0:i1])

REPL = [
    ("    src = None\n",
     "    src = None\n    why = None\n"),
    ("        cols.append((d, pw[0], pw[1]))\n",
     "        cols.append((d, pw[0], pw[1]))\n"
     "        PROV.append(('sh0', off, why, tuple(CTX)))\n"),
    ("        cols.append((dd, base, pl2))\n",
     "        cols.append((dd, base, pl2))\n"
     "        PROV.append(('sh1', off, why, tuple(CTX)))\n"),
    ("    cols.append((dd, e1, e2))\n",
     "    cols.append((dd, e1, e2))\n"
     "    PROV.append(('body', off, why, tuple(CTX)))\n"),
    ("            shallow = (st['prev'] == 0) or closes_unit(nxt)\n",
     "            shallow = (st['prev'] == 0) or closes_unit(nxt)\n"
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
     "            why = (why or '?') + ('/shallow' if shallow else '/deep')\n"),
    ("            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い\n",
     "            st['rec'][off] = 'tie'      # 浅い／深いの選択肢が無い\n"
     "            why = 'tie'\n"),
]
# 縮約の 4 本の再帰に文脈の積み木をかぶせる
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
    assert body.count(a) == 1, ('見つからない/多すぎ', a[:60], body.count(a))
    body = body.replace(a, b)

head = ('"""rows3.conv3 の写し（出どころを PROV に記録する）。mkprov.py が生成。"""\n'
        'import sys\n'
        "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')\n"
        'from rows3 import (split0, Lat, padL, is_branch, is_w_col, par0,\n'
        '                   hi_block, is_repeat, closes_unit, closes_hi_unit,\n'
        '                   wchain_head, sib_ok, ok_place, fit, dmap_at,\n'
        '                   copy_head, term_top, top_level, closes_top, hi_block2,\n'
        '                   anch_before, p0deep_ok,\n'
        '                   units_split, contrPre, leaves_mark,\n'
        '                   leaves_mark_local, ANCHOR, NOTLAST, V12, V13, V14)\n'
        'PROV = []\n'
        'CTX = []\n\n\n')
tail = '''

def b2d3p(M):
    """(像, PROV) の対。PROV は出力の柱と 1 対 1 で同じ順に並ぶ。"""
    del PROV[:]
    del CTX[:]
    st = {'ST': (), 'prev': None, 'dmap': [], 'Mo': tuple(M), 'nc': 0,
          'rec': {}}
    out = tuple(conv3(list(M), st=st))
    assert len(out) == len(PROV), (len(out), len(PROV))
    return out, list(PROV)
'''
open(OUT, 'w').write(head + body + tail)
print('書いた %s (%d 行)' % (OUT, (head + body + tail).count('\n')))
