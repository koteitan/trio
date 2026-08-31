"""縮約の pre が読む st['prev'] を差し替えられる写し rows3j.py（課題 H5 (3)）。"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {", """HX = {
    'prev_none': False,   # contrPre に None を渡す
    'prev_0': False,      # 0 を渡す
    'prev_1': False,      # 1 を渡す
    'prev_mat': False,    # 行列から読む: 直前の分岐列が深く綴られたか（近似）
}


def _prev_from_matrix(Mo, off):
    \"\"\"`st['prev']` の代わりに行列から読む近似。
    off より前の直近の分岐列 (a,1,0) を探し、その次の柱がユニットを閉じるなら 0、
    そうでなければ 1。分岐列が無ければ None。\"\"\"
    for j in range(off - 1, -1, -1):
        c = Mo[j]
        if c[0] == 0:
            return None
        if is_branch(c):
            nx = Mo[j + 1] if j + 1 < len(Mo) else None
            return 0 if closes_unit(nx) else 1
    return None


V12 = {""", 1)
old = "                pre = contrPre(p, U, A, e, ps[0], st['prev'], na)"
new = """                _pv = st['prev']
                if HX['prev_none']:
                    _pv = None
                elif HX['prev_0']:
                    _pv = 0
                elif HX['prev_1']:
                    _pv = 1
                elif HX['prev_mat']:
                    _pv = _prev_from_matrix(st['Mo'], off)
                pre = contrPre(p, U, A, e, ps[0], _pv, na)"""
assert src.count(old)==1
src = src.replace(old,new,1)
open('/tmp/h1work/rows3j.py','w').write(src)
print('ok')
