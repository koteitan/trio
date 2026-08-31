"""rows3.py の写しに、兄弟を本体の横に付ける条項（旗つき）を入れる。"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {", """SX = {
    'sibdd': False,      # 兄弟を本体の横 dd（＋本体の梯子 LA）に付ける
    'sibdd_w': False,    # 条件を「子に x w の柱がある かつ 子が 1 本でない」だけに
    'sibdd_l': False,    # 条件を「dd - d < 2」だけに
    'sibdd_nl': False,   # 梯子は LS のまま（深さだけ dd に）
    'sibdd_now': False,  # 「子が 1 本でない」を外す
    'sibdd_l2': False,   # 条項 (b) を「lad0 でなく、かつ dd == d+1」に絞る
    'sibdd_b2': False,   # (a) or (b2)
    'sibdd_z': False,    # (a) に「p の行 2 が 0 でない」を足す（z=0 断片を守る）
    'sibdd_zb': False,   # (a)+z or (b2)
    'aw2': False,        # after_w の枝を「nxt が閉じないなら深い」に置き換える
    'aw3': False,        # 同上 ＋ (hi かつ p[0] < 4) なら深い
}


def sib_dd_ok(Mo, off, oB, nA, d, dd, lad0=False):
    \"\"\"兄弟を本体の横 dd に付けるか（課題 H2）。

      (a) 引数ブロックに「x w」の柱 (k,0,0) があり、かつ引数が 1 本でない
      (b) 本体が影のすぐ下（dd - d < 2）

    教師データ（破れた対の証人 39 site / シートで壊れる 193 site）で
    正例 39/39 を覆い、負例の誤発火 0。
    \"\"\"
    a = (any(is_w_col(Mo[t]) for t in range(off + 1, oB))
         and (SX['sibdd_now'] or nA != 1))
    az = a and Mo[off][2] > 0
    b = (dd - d < 2)
    b2 = (not lad0) and (dd == d + 1)
    if SX['sibdd_w']:
        return a
    if SX['sibdd_l']:
        return b
    if SX['sibdd_l2']:
        return b2
    if SX['sibdd_b2']:
        return a or b2
    if SX['sibdd_z']:
        return az
    if SX['sibdd_zb']:
        return az or b2
    return a or b


V12 = {""", 1)
old = """    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB"""
new = """    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    dB, LB = d, LS
    if (B and (SX['sibdd'] or SX['sibdd_w'] or SX['sibdd_l']
               or SX['sibdd_l2'] or SX['sibdd_b2']
               or SX['sibdd_z'] or SX['sibdd_zb'])
            and sib_dd_ok(st['Mo'], off, oB, len(A), d, dd, lad0)):
        dB = dd
        if not SX['sibdd_nl']:
            LB = LA
    cB = conv3(B, dB, LB, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB"""
assert src.count(old)==1
src = src.replace(old,new,1)

o2 = """                shallow = not (hi and not pnt)\n"""
n2 = """                shallow = not (hi and not pnt)
                if SX['aw2'] or SX['aw3']:
                    _dq = not closes_unit(nxt)
                    if SX['aw3'] and hi and p[0] < 4:
                        _dq = True
                    shallow = not _dq\n"""
assert src.count(o2) == 1, src.count(o2)
src = src.replace(o2, n2, 1)
open('/tmp/h1work/rows3b.py','w').write(src)
print('ok')
