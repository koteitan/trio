# -*- coding: utf-8 -*-
"""H19: 「次の列」の見方を変える旗つきの写し rows3p.py（PXFLAGS=...）。

課題 R7 が出した反例は「末尾の分岐列が、**後ろに列が来ると綴りを変える**」型。
接頭辞単調（＝ 順序保存）にするには、綴りが `off` までの接頭辞だけで決まればよい。

  endopen   行列の末尾では「後ろに列がある」ものとして扱う
            （`closes_unit(None)` を False に、`onx=None` を非閉に）
  noclose   `closes_unit(nxt)` の項を落とす（`prev==0` だけで浅くする）
  endopen_b `endopen` を分岐列の基本判定だけに掛ける
"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
HEAD = ("PX = {'endopen': False, 'noclose': False, 'endopen_b': False}\n"
        "for _k in os.environ.get('PXFLAGS', '').split(','):\n"
        "    if _k.strip():\n"
        "        assert _k.strip() in PX, _k\n"
        "        PX[_k.strip()] = True\n\n\nV12 = {")
src = src.replace("V12 = {", HEAD, 1)
GATE = '\n'.join([
 "def closes_px(nxt, at_end):",
 "    # H19: 行列の末尾（nxt is None）を「まだ続く」と読む",
 "    if nxt is None and (PX['endopen'] or (PX['endopen_b'] and at_end)):",
 "        return False",
 "    return closes_unit(nxt)",
 "",
 "",
 ""])
src = src.replace('def _snap(st):', GATE + 'def _snap(st):', 1)
R = [
 ("            shallow = (st['prev'] == 0) or closes_unit(nxt)",
  "            shallow = (st['prev'] == 0) or (\n"
  "                False if PX['noclose'] else closes_px(nxt, True))"),
 ("            if st['prev'] == 1 and is_w_col(pv) and closes_unit(onx):",
  "            if st['prev'] == 1 and is_w_col(pv) and closes_px(onx, False):"),
 ("            elif V13['wchain'] and st['prev'] == 1 and closes_unit(onx):",
  "            elif V13['wchain'] and st['prev'] == 1 and closes_px(onx, False):"),
]
for a, b in R:
    assert src.count(a) == 1, ('見つからない', a[:50])
    src = src.replace(a, b, 1)
open('/tmp/h1work/rows3p.py', 'w').write(src)
print('ok')
