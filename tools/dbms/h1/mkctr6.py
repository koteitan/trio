"""縮約のあとの兄弟 cB に first=True を渡せる写し rows3h.py。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", """EX = {
    'cbfirst': False,    # 縮約のあとの兄弟 cB に first=True を渡す（入れ子の縮約を許す）
    'cbforce': False,    # 同上 ＋ force=True
    'sbfirst': False,    # 縮約なしの兄弟 cB にも first=True
}


V12 = {""", 1)
old = """            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
new = """            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2),
                       bool(EX['cbfirst'] or EX['cbforce']),
                       bool(EX['cbforce']), st, nx, oBq)"""
assert src.count(old)==1
src = src.replace(old,new,1)
old2 = """    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB"""
new2 = """    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), bool(EX['sbfirst']), False,
               st, nx, oB)
    return cols + cA + cB"""
assert src.count(old2)==1
src = src.replace(old2,new2,1)
open('/tmp/h1work/rows3h.py','w').write(src)
print('ok')
