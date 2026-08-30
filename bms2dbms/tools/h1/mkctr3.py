"""縮約の中の cB（縮約のあとの兄弟）と cA の深さ／梯子を旗で変える写し rows3d.py。"""
src = open('/home/koteitan/proofs/dbms/bms2dbms/tools/rows3.py').read()
src = src.replace("sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))",
                  "sys.path.insert(0, '/home/koteitan/proofs/dbms/bms2dbms/tools')")
src = src.replace("V12 = {", """DX = {
    'cbd1': False,     # 縮約の cB を d+1 に
    'cbdd': False,     # 縮約の cB を dd に
    'cbde': False,     # 縮約の cB を d+1+e に
    'cbla': False,     # 縮約の cB の梯子を LA に（深さは別の旗で）
    'cblr': False,     # 縮約の cB の梯子を Lr に
}


V12 = {""", 1)
old = """            cB = conv3(Bq, d, L, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
new = """            _dB = d
            if DX['cbd1']:
                _dB = d + 1
            elif DX['cbdd']:
                _dB = dd
            elif DX['cbde']:
                _dB = d + 1 + e
            _LB = L
            if DX['cbla']:
                _LB = LA
            elif DX['cblr']:
                _LB = Lr
            cB = conv3(Bq, _dB, _LB, FA, (v, s2), (e1, e2), False, False, st, nx,
                       oBq)"""
assert src.count(old)==1
src = src.replace(old,new,1)
open('/tmp/h1work/rows3d.py','w').write(src)
print('ok')
