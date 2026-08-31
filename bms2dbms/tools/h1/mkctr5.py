"""縮約のどの門で落ちたかを記録する写し rows3g.py（現行の rows3.py に合わせる）。"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {", "CTRLOG = []\n\n\nV12 = {", 1)
R = [
 ("            U, B2 = units_split(p, B, qlab)\n            if not B2:\n                continue\n",
  "            U, B2 = units_split(p, B, qlab)\n            if not B2:\n                CTRLOG.append((off, e, 'B2 が空')); continue\n"),
 ("            if (q[1], q[2]) != qlab or q[0] != p[0]:\n                continue\n",
  "            if (q[1], q[2]) != qlab or q[0] != p[0]:\n                CTRLOG.append((off, e, 'q のラベル違い %s' % (tuple(q),))); continue\n"),
 ("                    break\n            else:\n                continue\n",
  "                    break\n            else:\n                CTRLOG.append((off, e, 'pre が合わない')); continue\n"),
 ("                if rest2[0][0] < p[0] + 1:\n                    continue\n",
  "                if rest2[0][0] < p[0] + 1:\n                    CTRLOG.append((off, e, '残余が浅い')); continue\n"),
 ("                        and (rest2[0][1], rest2[0][2]) >= (v + e, s2) and e == 0):\n                    continue\n",
  "                        and (rest2[0][1], rest2[0][2]) >= (v + e, s2) and e == 0):\n                    CTRLOG.append((off, e, '残余の行1')); continue\n"),
 ("            elif e == 0 or not deep_end:\n",
  "            elif e == 0 or not deep_end:\n                CTRLOG.append((off, e, '残余なし: e=0 か deep_end でない'))\n"),
 ("            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数\n",
  "            CTRLOG.append((off, e, 'FIRE'))\n            st['nc'] = st.get('nc', 0) + 1      # 縮約が発火した回数\n"),
]
for a,b in R:
    assert src.count(a)>=1, ('miss', a[:60])
    src = src.replace(a,b,1)
open('/tmp/h1work/rows3g.py','w').write(src)
print('ok')
