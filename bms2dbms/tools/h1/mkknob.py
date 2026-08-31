# -*- coding: utf-8 -*-
"""H17: 縮約まわりの「つまみ」を独立に入れ切りできる写し rows3k2.py（KFLAGS=a,b）。

  cbd1    縮約の兄弟 `cB` の深さを d+1
  crd1    縮約の残余 `cR` の深さを rd+1
  sb      影の兄弟を本体の横 dd に付ける（非縮約の枝）
  sb_w    同上、兄弟の頭が「x w」のときだけ
  cbls    `cB` に `LS`（sibL つき梯子）を渡す
  cbfa    `cB` に F の代わりに空タプルを渡す
  cbfirst `cB` に `first_of` を渡す
  sdall   tie で常に base_sd を使う
  sibnball `sibnb_ok` の門を外す
  awall   `after_w` の決定を常に反転
"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
HEAD = ("KN = dict.fromkeys(['cbd1','crd1','sb','sb_w','cbls','cbfa','cbfirst',\n"
        "                    'sdall','sibnball','awall'], False)\n"
        "for _k in os.environ.get('KFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in KN, _k\n"
        "        KN[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
R = [
 ("""            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)""",
  """            cB = conv3(Bq, d + (1 if (KN['cbd1'] and Bq) else 0),
                       LS if KN['cbls'] else L,
                       () if KN['cbfa'] else FA, (v, s2), (e1, e2),
                       first_of(st['Mo'], oBq) if KN['cbfirst'] else False,
                       False, st, nx, oBq)"""),
 ("            cR = conv_resid(rest2, rd, Lr, (v, s2), (e1, e2), st, hd(Bq), oR)",
  "            cR = conv_resid(rest2, rd + (1 if (KN['crd1'] and rest2) else 0),\n"
  "                            Lr, (v, s2), (e1, e2), st, hd(Bq), oR)"),
 ("    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)",
  "    dB = d\n"
  "    if (KN['sb'] and lad1 and B and dd > d\n"
  "            and (not KN['sb_w'] or (B[0][1] == 0 and B[0][2] == 0))):\n"
  "        dB = dd\n"
  "    cB = conv3(B, dB, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)"),
 ("""            if (V18['tiesd'] and base_sd != deep
                    and tie_sd(st['Mo'], off)):
                base = base_sd""",
  """            if (base_sd != deep and (KN['sdall'] or
                    (V18['tiesd'] and tie_sd(st['Mo'], off)))):
                base = base_sd"""),
 ("""        if (V16['sibnb'] and v >= 1 and base_sd != base_d
                and sib_ok(off, src, st) and sibnb_ok(st['Mo'], off)):""",
  """        if (V16['sibnb'] and v >= 1 and base_sd != base_d
                and sib_ok(off, src, st)
                and (KN['sibnball'] or sibnb_ok(st['Mo'], off))):"""),
 ("""                if V17['awflip'] and aw_flip(Mo, off):
                    shallow = not shallow""",
  """                if V17['awflip'] and (KN['awall'] or aw_flip(Mo, off)):
                    shallow = not shallow"""),
]
for a, b in R:
    assert src.count(a) == 1, ('見つからない', a[:50])
    src = src.replace(a, b, 1)
open('/tmp/h1work/rows3k2.py', 'w').write(src)
print('ok')
