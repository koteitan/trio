"""rows3.py の写しで、兄弟の深さを site ごとに dd に強制できるようにする。"""
src = open('/home/koteitan/proofs/dbms/tools/dbms/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/tools/dbms')")
src = src.replace("V12 = {", """SIBFORCE = set()        # ここに入れた親の off では 兄弟を dd に付ける
SIBSITES = []           # 走らせたときに通った兄弟の site を記録
SIBREC = [False]
SIBMODE = [1]


V12 = {""", 1)
old = """    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    cB = conv3(B, d, LS, FA, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB"""
new = """    cA = conv3(A, dd + 1, LA, FA, (v, s2), (e1, e2), True, f0, st,
               B[0] if B else nx, oA)
    dB = d
    if B:
        if SIBREC[0]:
            SIBSITES.append(dict(off=off, oB=oB, d=d, dd=dd, lad0=lad0,
                                 lad1=lad1, v=v, s2=s2, e1=e1, e2=e2,
                                 base=base, nA=len(A), nB=len(B)))
        if off in SIBFORCE:
            dB = dd
    LB, FB = LS, FA
    if B and off in SIBFORCE:
        md = SIBMODE[0]
        if md == 2:
            LB, FB = LA, FA
        elif md == 3:
            LB, FB = LA, F
        elif md == 4:
            LB, FB = padL(Lb, v) + ((e1, s2, fc, e1),), F
        elif md == 5:
            LB, FB = Lb, FA
    cB = conv3(B, dB, LB, FB, (v, s2), (e1, e2), False, False, st, nx, oB)
    return cols + cA + cB"""
assert src.count(old)==1
src = src.replace(old,new,1)
open('/tmp/h1work/rows3sib.py','w').write(src)
print('ok')
