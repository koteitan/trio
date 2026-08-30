"""縮約の cB を site ごとに d+1 に強制できる写し rows3e.py。"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {", """CBFORCE = set()     # ここに入れた縮約の親の off では cB を d+1 に
CBSITES = []        # 通った cB の site を記録
CBREC = [False]


V12 = {""", 1)
old = """            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
new = """            if Bq:
                if CBREC[0]:
                    CBSITES.append(dict(off=off, oBq=oBq, d=d, dd=dd, e=e,
                                        v=v, s2=s2, e1=e1, e2=e2, base=base,
                                        nA=len(A), nU=len(U), nR=len(rest2),
                                        nBq=len(Bq), lad0=lad0, lad1=lad1,
                                        deep_end=deep_end, rd=rd))
            _dB = d + 1 if (Bq and off in CBFORCE) else d
            cB = conv3(Bq, _dB, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
assert src.count(old)==1
src = src.replace(old,new,1)
open('/tmp/h1work/rows3e.py','w').write(src)
print('ok')
